(* reloc-zl14c *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_len1 Zg_infl_c_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST RefInflateA_LEN1 RefInflateA_LEN RefInflateSafeOK RefInflateSafeOK2. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import InffastMem RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation pullr := RefInflateArmLib.pullr.
Lemma len_pre : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_LEN q ms -> DE X r q -> ix_ok X -> REGS c r -> PATG X (mkW s c r) -> 0 <= is_lenbits s <= 15 ->
  (ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_back s 0) c r) PC_LEN_D q' ms' /\ DE X r q'
                                   /\ h11 q' = wz (is_lenbits s) /\ h12 q' = wz 31) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) XO HREGS HP RN HSLOW.
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh HL.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  assert (HAV : ir_have r < 2^31 /\ ir_left r < 2^31) by (rewrite Pin in Rnh; rewrite Pout in Rpl; lia).
  clear RH Rin. ix_open XO. unfold PC_LEN.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 3 zs. br_cases KG; [| do 2 zs; br_cases KL; [| do 2 zs; br_true]]; do 4 zs;
  itr_groups MUf WMf;
  (apply evt_done; eexists; split; [eapply ILOOPh_intro; ired; [ireg .. |]| unfold DE; cbn [h9 h10 h11 h12 h18 h22 h24 h25]; repeat split; reflexivity]);
  (apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ]).
Qed.
Definition PC_LEN_L1 : Z := 0x20e7c.
Definition LL1 (X : ictx) (s : inflate_state) (r0 r : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r)) in
  h19 q = wz (code_w e) /\ h7 q = wz (code_bits e) /\ h28 q = wz (code_w e ≫ 8)
  /\ h16 q = wz (ir_bits r) /\ h11 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h12 q = wz (ir_have r) /\ h17 q = wz (ir_have r) /\ h5 q = wz (8 * ir_have r)
  /\ h14 q = wz (il_NI (ix_L X) + ir_next r) /\ h6 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h29 q = wz (Z.ones (is_lenbits s)) /\ h13 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz 1
  /\ h30 q = wz (Z.shiftl (ir_have r0) 32) /\ h24 q = wz (ir_have r0) /\ h25 q = wz (il_NI (ix_L X) + ir_next r0) /\ h18 q = wz (ir_bits r0)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).
Lemma len_loop1 : forall k X s c r0 r rf q ms,
  ILOOPh X (mkW s c r) PC_LEN_L1 q ms -> LL1 X s r0 r q ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_bits r0 -> 0 <= ir_have r0 < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  ir_bits r < code_bits (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r))) ->
  dchk k c (dec_idx1 (is_lenbits s)) code_bits (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r = Some rf ->
  evt usegs (DECG X s c rf r0 (DECODE_k k (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits (mkW s c r)) rf
               (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_LEN_J1 (len_Q1 X s r0)) ms.
Proof.
  induction k as [|k IH]; intros X s c r0 r rf [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms
    HL HQ XO HREGS HPL HB0 HH0 Pin Pin1 RN CPO HB HD.
  { exfalso. exact (CK_short0 _ _ _ _ _ _ _ HD HB). }
  destruct HL as (m & -> & HMEM). unfold LL1 in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E19 & E7 & E28 & E16 & E11 & E22 & E12 & E17 & E5 & E14 & E6 & E29 & E13 & E15 & E30 & E24 & E25 & E18 & E9 & E10). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r0 r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (ones_range15 n RN) as RMK.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0].
  set (e0 := code_at s p (dec_idx1 n (ir_hold r))) in *. pose proof (code_w_range e0) as RW0. pose proof (code_bits_range e0) as RB0.
  unfold PC_LEN_L1. ix_open XO.
  zstep. br_cases K.
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (DC_dry k p (dec_idx1 n) code_bits s c r) by (subst e0; lia).
    do 9 zs. rewrite ?land_ones32, ?shl3, ?shl32_shr32 by lia.
    apply evt_done. right. exists r. split; [reflexivity|]. split; [exact HPL|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
  -
    pose proof (CK_pull _ _ _ _ _ _ _ _ HD HB ltac:(lia)) as HD'.
    rewrite (DC_pull k p (dec_idx1 n) code_bits s c r) by (subst e0; lia).
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r0 r HREGS HB0 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7 & E8 & E9' & RH1).
    assert (RH1' : 0 <= ir_hold (pullr c r) < 2^64).
    { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
    apply (id : _ -> hide _) in RH1.
    do 2 zs. gF. zs. gF.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    replace (arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r) with (ir_hold (pullr c r)) by lia.
    pose proof (dec_idx1_land n (ir_hold (pullr c r)) ltac:(lia) RN) as EI1. pose proof (dec_idx1_range n (ir_hold (pullr c r)) ltac:(lia) RN) as RI1'.
    set (h1 := ir_hold (pullr c r)) in *.
    zs. rewrite EI1. destruct (CK_range _ _ _ _ _ _ _ _ HD') as [RI1 RN1]. fold h1 in RI1, RN1.
    set (i1 := dec_idx1 n h1) in *. set (e1 := code_at s p i1) in *. pose proof (code_bits_range e1) as RB1. pose proof (code_w_range e1) as RW1.
    pose proof (cp_addr_rng (ix_L X) p i1 CPO RI1 ltac:(lia)) as CPR1.
    zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gF.
    do 6 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
    do 2 zs.
    pose proof (code_rd_val m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2 + 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e1); lia). clear RD.
    pose proof (code_rd_lo m (ix_L X) s p i1 (wa (cp_addr (ix_L X) p + i1 ≪ 2)) MI Gc CPO RI1 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    fold e1 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e1); lia). clear RD.
    do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits.
    zstep. br_cases K3.
    +
      assert (K3' : code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h1; fold i1; fold e1; lia).
      rewrite (DC_found k p (dec_idx1 n) code_bits s c (pullr c r)) by exact K3'.
      destruct (CK_found _ _ _ _ _ _ _ _ HD' K3') as [_ ->].
      apply evt_done. left. eexists (pullr c r), _. split; [reflexivity|]. split; [reflexivity|]. split; [exact K3'|]. split; [subst i1 h1; exact RI1|].
      split; [exact HREGS1|]. split; [exact HPL1|]. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
      unfold hide in RH1. unfold len_Q1. hred. subst e1 i1 h1 p n.
      repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; lia ].
    +
      assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; lia).
      eapply (IH X s c r0 (pullr c r) rf);
        [ eapply ILOOPh_intro; try reflexivity; exact HMEM
        | unfold hide in RH1; unfold LL1; hred; subst e1 i1 h1 p n; repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; lia ]
        | exact XO | exact HREGS1 | exact HPL1 | exact HB0 | exact HH0 | exact Pin | exact Pin1 | exact RN | exact CPO | exact K3' | exact HD' ].
Qed.
Lemma len_lvl1 : forall X s c r rf q ms,
  ILOOPh X (mkW s c r) PC_LEN_D q ms -> DE X r q -> h11 q = wz (is_lenbits s) -> h12 q = wz 31 -> ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  0 <= is_lenbits s <= 15 -> cp_ofs_ok (is_lencode s) ->
  dchk 8 c (dec_idx1 (is_lenbits s)) code_bits (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r = Some rf ->
  evt usegs (DECG X s c rf r (DECODE_k 8 (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits (mkW s c r)) rf
               (is_lencode s) (dec_idx1 (is_lenbits s)) code_bits PC_LEN_J1 (len_Q1 X s r)) ms.
Proof.
  intros X s c r rf [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) E11 E12 XO HREGS HP RN CPO HD.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x9 x10 x18 x22 x24 x25 x11 x12.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST. open_isA GA.
  unfold PC_LEN_D. ix_open XO.
  set (p := is_lencode s) in *. set (n := is_lenbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0]. pose proof (ones_range15 n RN) as RMK.
  gF. do 4 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
  set (i0 := dec_idx1 n (ir_hold r)) in *. set (e0 := code_at s p i0) in *.
  pose proof (code_bits_range e0) as RB0. pose proof (cp_addr_rng (ix_L X) p i0 CPO RI0 ltac:(lia)) as CPR.
  zs. rewrite (Z.shiftl_mul_pow2 i0 2) by lia. change (2^2) with 4. zs. gF. do 3 zs. gX.
  replace (0 <? cp_addr (ix_L X) p) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  do 9 zs. rewrite !land_u32_small by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2 + 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e0); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i0 (wa (cp_addr (ix_L X) p + i0 ≪ 2)) MI Gc CPO ltac:(lia) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e0 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e0); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. pose proof (code_w_range e0) as RW0. do 2 zs. rewrite code_w_bits.
  rewrite (shl32_shr29 (ir_have r)) by lia.
  zstep. br_cases K.
  -
    rewrite (DC_found 8 p (dec_idx1 n) code_bits s c r) by (fold i0; fold e0; lia).
    destruct (CK_found _ _ _ _ _ _ _ _ HD ltac:(fold i0; fold e0; lia)) as [_ ->].
    apply evt_done. left. eexists r, _. split; [reflexivity|]. split; [reflexivity|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [exact HREGS|]. split; [apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)]|].
    split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
    unfold len_Q1. hred. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    eapply (len_loop1 8%nat X s c r r rf);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM
      | unfold hide in RH; unfold LL1; hred; subst e0 i0 p n; repeat split; first [ reflexivity | ireg | f_equal; lia | rewrite Z.shiftl_mul_pow2 by lia; ireg ]
      | exact XO | exact HREGS | apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1 | exact RN | exact CPO | exact K' | exact HD ].
Qed.
Lemma len_two_cases : forall op, 0 <= op < 256 -> len_two op = false -> op = 0 \/ 16 <= op.
Proof.
  intros op Hop H. unfold len_two in H. destruct (Z.eqb_spec op 0) as [E|NE]; [left; exact E| right].
  cbn [negb andb] in H. rewrite (land240_le15 _ Hop) in H. apply Z.leb_gt in H. lia.
Qed.
Lemma len_two_true : forall op, 0 <= op < 256 -> len_two op = true -> 1 <= op <= 15.
Proof.
  intros op Hop H. unfold len_two in H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite (land240_le15 _ Hop) in H2. apply Z.leb_le in H2. apply negb_true_iff in H1. apply Z.eqb_neq in H1. lia.
Qed.
Lemma len_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J1 q ms -> len_Q1 X s r0 r1 q -> ix_ok X ->
  len_two (code_op (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)))) = false ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1))) r1 0 r0 q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO TWO.
  destruct HQ as (E19 & E7 & E28 & E16 & E11 & E22 & E12 & E17 & E5 & E14 & E6 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh_keep HL HMEM.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_w_range e) as RW.
  ix_open XO. unfold PC_LEN_J1.
  zs. rewrite code_w_op.
  destruct (len_two_cases _ ROP TWO) as [E0|K16].
  - rewrite E0. do 2 zs. zstep. br_true. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29]. rewrite E0. repeat split; reflexivity.
  - do 2 zs. zstep. br_true. do 2 zs.
    apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold len_QT. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29]. repeat split; reflexivity.
Qed.
Definition PC_LEN_L2 : Z := 0x20f74.
Definition LL2 (X : ictx) (s : inflate_state) (last : Z) (r0 r1 r : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_lencode s) (dec_idx2 last (ir_hold r)) in
  h19 q = wz (code_w e) /\ h23 q = wz (code_w e ≫ 8) /\ h24 q = wz (code_bits e + code_bits last) /\ h21 q = wz (ir_bits r)
  /\ h22 q = wz (ir_hold r) /\ h12 q = wz (ir_have r) /\ h31 q = wz (il_NI (ix_L X) + ir_next r) /\ h6 q = wz (il_NI (ix_L X) + ir_next r)
  /\ h11 q = wz (ir_bits r1) /\ h16 q = wz (ir_bits r1) /\ h17 q = wz (ir_have r1) /\ h5 q = wz (8 * ir_have r1) /\ h14 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h18 q = wz (code_bits last + ir_bits r1 - ir_bits r)
  /\ h7 q = wz (code_bits last) /\ h29 q = wz (code_val last) /\ h30 q = wz (Z.ones (code_bits last + code_op last)) /\ h28 q = wz (code_w last ≫ 8)
  /\ h13 q = wz (cp_addr (ix_L X) (is_lencode s)) /\ h15 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).
Lemma len_loop2 : forall k X s c r0 r1 r rf last q ms,
  ILOOPh X (mkW s c r) PC_LEN_L2 q ms -> LL2 X s last r0 r1 r q ->
  ix_ok X -> REGS c r -> pulled r1 r -> 0 <= ir_bits r1 -> 0 <= ir_have r1 < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  ir_put r1 = ir_put r0 ->
  cp_ofs_ok (is_lencode s) -> 0 <= code_bits last -> 0 <= code_op last -> code_bits last + code_op last <= 31 -> 0 <= code_val last < 2^16 ->
  ir_bits r < dec_need2 last (code_at s (is_lencode s) (dec_idx2 last (ir_hold r))) ->
  dchk k c (dec_idx2 last) (dec_need2 last) (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r = Some rf ->
  evt usegs (DECG X s c rf r1 (DECODE_k k (is_lencode s) (dec_idx2 last) (dec_need2 last) (mkW s c r)) rf
               (is_lencode s) (dec_idx2 last) (dec_need2 last) PC_LEN_J2 (len_Q2 X s last r1)) ms.
Proof.
  induction k as [|k IH]; intros X s c r0 r1 r rf last [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms
    HL HQ XO HREGS HPL HB1 HH1 Pin Pin1 EP CPO RLB ROP K31 RVAL HB HD.
  { exfalso. exact (CK_short0 _ _ _ _ _ _ _ HD HB). }
  destruct HL as (m & -> & HMEM). unfold LL2 in HQ. hred_in HQ. cbn [w_s w_c w_r] in HMEM.
  destruct HQ as (E19 & E21 & E23 & E20 & E22 & E12 & E31 & E6 & E11 & E16 & E17 & E5 & E14 & E18 & E7 & E29 & E30 & E28 & E13 & E15 & E9 & E10). subst. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r1 r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r1 r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  set (p := is_lencode s) in *.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  pose proof (code_w_range last) as RWL.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0].
  set (e0 := code_at s p (dec_idx2 last (ir_hold r))) in *. pose proof (code_w_range e0) as RW0. pose proof (code_bits_range e0) as RB0.
  unfold PC_LEN_L2. ix_open XO.
  zstep. br_cases K.
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (DC_dry k p (dec_idx2 last) (dec_need2 last) s c r) by (subst e0; lia).
    do 7 zs.
    apply evt_done. right. exists r. split; [reflexivity|]. split; [exact HPL|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
  -
    pose proof (CK_pull _ _ _ _ _ _ _ _ HD HB ltac:(lia)) as HD'.
    rewrite (DC_pull k p (dec_idx2 last) (dec_need2 last) s c r) by (subst e0; lia).
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r1 r HREGS HB1 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7' & E8 & E9' & RH1).
    assert (RH1' : 0 <= ir_hold (pullr c r) < 2^64).
    { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
    apply (id : _ -> hide _) in RH1.
    do 2 zs. gF. zs. gF.
    pose proof (u8ro_read usegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    replace (arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r) with (ir_hold (pullr c r)) by lia.
    set (h2 := ir_hold (pullr c r)) in *.
    pose proof (land_ones_le h2 (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
    assert (EI3 : (Z.land h2 mk2 ≫ code_bits last) + code_val last = dec_idx2 last h2) by (subst mk2; rewrite dec_idx2_clang by lia; reflexivity).
    zs. set (hm3 := Z.land h2 mk2) in *.
    pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
    zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
    zs. rewrite EI3.
    destruct (CK_range _ _ _ _ _ _ _ _ HD') as [RI3 RN3]. fold h2 in RI3, RN3.
    set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3. pose proof (code_w_range e3) as RW3.
    assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
    rewrite EN3 in *.
    pose proof (cp_addr_rng (ix_L X) p i3 CPO RI3 ltac:(lia)) as CPR3.
    do 2 zs. rewrite (zext32_x4 i3) by lia. zs. gF.
    do 3 zs. rewrite (land_u32_small i3) by lia. do 2 zs. rewrite xor_guard1 by lia. do 2 zs. zstep. br_true.
    do 2 zs.
    pose proof (code_rd_val m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2 + 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e3); lia). clear RD.
    pose proof (code_rd_lo m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + i3 ≪ 2)) MI Gc CPO RI3 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
    fold e3 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e3); lia). clear RD.
    do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
    zstep. br_cases K3.
    +
      assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h2; fold i3; fold e3; rewrite EN3; lia).
      rewrite (DC_found k p (dec_idx2 last) (dec_need2 last) s c (pullr c r)) by exact K3'.
      destruct (CK_found _ _ _ _ _ _ _ _ HD' K3') as [_ ->].
      apply evt_done. left. eexists (pullr c r), _. split; [reflexivity|]. split; [reflexivity|]. split; [exact K3'|]. split; [subst i3 h2; exact RI3|].
      split; [exact HREGS1|]. split; [exact HPL1|]. split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
      unfold hide in RH1. unfold len_Q2. hred. subst e3 i3 sh3 hm3 h2 mk2 p.
      repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6', ?EP; ireg | f_equal; lia ].
    +
      assert (K3' : ir_bits (pullr c r) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r))))) by (fold h2; fold i3; fold e3; rewrite EN3; lia).
      eapply (IH X s c r0 r1 (pullr c r) rf last);
        [ eapply ILOOPh_intro; try reflexivity; exact HMEM
        | unfold hide in RH1; unfold LL2; hred; subst e3 i3 sh3 hm3 h2 mk2 p; repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; lia ]
        | exact XO | exact HREGS1 | exact HPL1 | exact HB1 | exact HH1 | exact Pin | exact Pin1 | exact EP
        | exact CPO | exact RLB | exact ROP | exact K31 | exact RVAL | exact K3' | exact HD' ].
Qed.
Lemma len_lvl2 : forall X s c r0 r1 rf q ms,
  ILOOPh X (mkW s c r1) PC_LEN_J1 q ms -> len_Q1 X s r0 r1 q -> ix_ok X -> PATG X (mkW s c r0) ->
  ir_put r1 = ir_put r0 -> REGS c r1 ->
  0 <= dec_idx1 (is_lenbits s) (ir_hold r1) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  forall last, last = code_at s (is_lencode s) (dec_idx1 (is_lenbits s) (ir_hold r1)) ->
  len_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dchk 8 c (dec_idx2 last) (dec_need2 last) (ctab_size (is_lencode s)) (code_at s (is_lencode s)) r1 = Some rf ->
  evt usegs (DECG X s c rf r1 (DECODE_k 8 (is_lencode s) (dec_idx2 last) (dec_need2 last) (mkW s c r1)) rf
               (is_lencode s) (dec_idx2 last) (dec_need2 last) PC_LEN_J2 (len_Q2 X s last r1)) ms.
Proof.
  intros X s c r0 r1 rf [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EP HREGS
         RI CPO last ELAST TWO KB K31 HD.
  destruct HQ as (E19 & E7 & E28 & E16 & E11 & E22 & E12 & E17 & E5 & E14 & E6 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x7 x28 x16 x11 x22 x12 x17 x5 x14 x6 x13 x15 x9 x10.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r] in HMEM. hred.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_lencode s) in *. set (i := dec_idx1 (is_lenbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS. pose proof (code_w_range last) as RWL.
  pose proof (len_two_true _ ROP TWO) as K15.
  pose proof (REGS_hold64 c r1 HREGS) as RH64.
  assert (HAV : ir_have r1 < 2^31) by (rewrite Pin in Rnh; lia).
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH.
  open_IST ST. ix_open XO. unfold PC_LEN_J1.
  zs. rewrite code_w_op. do 3 zs. br_false.
  do 2 zs. rewrite code_w_ge000 by lia. gF.
  zs. rewrite code_w_op. do 2 zs. gF.
  zs. rewrite code_w_val.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 3 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  zs.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI2 RN2].
  do 2 zs. rewrite (zext32_x4 (sh + code_val last)) by lia. rewrite EI2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2. pose proof (code_w_range e2) as RW2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  pose proof (cp_addr_rng (ix_L X) p i2 CPO RI2 ltac:(lia)) as CPR2.
  zs. gF. do 2 zs. rewrite xor_guard1 by lia. zstep. br_false. zs. do 3 zs. rewrite (land_u32_small i2) by lia.
  do 2 zs.
  pose proof (code_rd_val m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2 + 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_val_range e2); lia). clear RD.
  pose proof (code_rd_lo m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + i2 ≪ 2)) MI Gc CPO RI2 ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD.
  fold e2 in RD. zs. rewrite zx16_small by (pose proof (code_lo_range e2); lia). clear RD.
  do 2 zs. rewrite code_w_or_step. do 2 zs. rewrite code_w_bits. zs.
  zstep. br_cases K.
  -
    assert (K' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1))) <= ir_bits r1) by (fold i2; fold e2; rewrite EN2; lia).
    rewrite (DC_found 8 p (dec_idx2 last) (dec_need2 last) s c r1) by exact K'.
    destruct (CK_found _ _ _ _ _ _ _ _ HD K') as [_ ->].
    apply evt_done. left. eexists r1, _. split; [reflexivity|]. split; [reflexivity|]. split; [exact K'|]. split; [exact RI2|].
    split; [exact HREGS|]. split; [apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)]|].
    split; [eapply ILOOPh_intro; try reflexivity; exact HMEM|].
    unfold len_Q2. hred. fold p. fold i2. fold e2. rewrite EP. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; lia).
    eapply (len_loop2 8%nat X s c r0 r1 r1 rf last);
      [ eapply ILOOPh_intro; try reflexivity; exact HMEM
      | unfold hide in RH; unfold LL2; hred; subst e2 i2 sh hm mk2 p i; repeat split; first [ reflexivity | ireg | f_equal; lia ]
      | exact XO | exact HREGS | apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1 | exact EP
      | exact CPO | lia | lia | exact K31 | exact RVAL | exact K' | exact HD ].
Qed.
Lemma len_j2 : forall X s c r0 r1 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_LEN_J2 q ms -> len_Q2 X s last r1 r2 q -> ix_ok X -> PATG X (mkW s c r0) ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_lencode s) -> cp_ofs_ok (is_lencode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_bits r1 <= 63 -> code_bits last + code_op last <= 31 ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) -> ir_put r1 = ir_put r0 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (iset_back s (code_bits last)) c r0) PC_LEN_T q' ms'
                                   /\ len_QT X (code_at s (is_lencode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last)) (code_bits last) r0 q') ms.
Proof.
  intros X s c r0 r1 r2 last [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RI CPO RB RH RB1 K31 RPUT EP.
  destruct HQ as (E19 & E21 & E23 & E20 & E22 & E12 & E31 & E11 & E16 & E17 & E5 & E14 & E18 & E7 & E29 & E28 & E13 & E15 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x23 x24 x21 x22 x12 x31 x11 x16 x17 x5 x14 x18 x7 x29 x28 x13 x15 x9 x10.
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_lencode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_bits_range e) as RBITS. pose proof (code_w_range e) as RWE.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO. pose proof (code_w_range last) as RWL.
  ix_open XO. unfold PC_LEN_J2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r0) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  zs. rewrite code_w_op. zs. rewrite subw_land64 by lia. zs. rewrite code_w_g31 by lia. zs. rewrite (land63_small (code_bits last)) by lia.
  do 4 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
  - apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA
                          | unfold isT, isT_cells; exists padT; inorm; close_cells GT
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - unfold len_QT, ddrop. cbn [h7 h9 h10 h11 h12 h14 h19 h22 h28 h29 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
    rewrite EP. repeat split; try reflexivity. all: rewrite ?wrap32_id by lia; f_equal; lia.
Qed.
