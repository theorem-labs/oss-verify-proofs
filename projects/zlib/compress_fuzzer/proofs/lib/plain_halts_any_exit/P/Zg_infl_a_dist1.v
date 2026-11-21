(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Zg_infl_c_kit.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST RefInflateSafeOK RefInflateSafeOK2 InffastMem RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Notation pullr := RefInflateArmLib.pullr.

Definition PC_DIST_L1 : Z := 0x1e8a8.
Definition PC_DIST_J1 : Z := 0x1e8f0.
Definition dist_Q1 (X : ictx) (s : inflate_state) (r1 : iregs) (q : iscrh) : Prop :=
  h12 q = wz (ir_have r1) /\ h13 q = wz (ir_bits r1) /\ h27 q = wz (il_NI (ix_L X) + ir_next r1) /\ h22 q = wz (ir_hold r1)
  /\ h14 q = wz (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))))
  /\ h16 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx1 (is_distbits s) (ir_hold r1))
  /\ h15 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma dist_loop1 : forall k X s c r0 r rf q ms,
  ILOOPh X (mkW s c r0) PC_DIST_L1 q ms ->
  h9 q = wz (ir_have r0) -> h23 q = wz (ir_bits r0) -> h26 q = wz (il_NI (ix_L X) + ir_next r0) ->
  h12 q = wz (ir_have r) -> h13 q = wz (ir_bits r) -> h5 q = wz (ir_bits r) -> h6 q = wz (il_NI (ix_L X) + ir_next r) -> h22 q = wz (ir_hold r) ->
  h16 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx1 (is_distbits s) (ir_hold r)) ->
  h14 q = wz (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r)))) ->
  h17 q = wz (Z.ones (is_distbits s)) -> h15 q = wz (cp_addr (ix_L X) (is_distcode s)) -> h29 q = wz 30 -> h31 q = wz (-16180) ->
  ix_ok X -> REGS c r -> pulled r0 r -> 0 <= ir_bits r0 -> 0 <= ir_have r0 < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  0 <= is_distbits s <= 15 -> cp_ofs_ok (is_distcode s) ->
  ir_bits r < code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r))) ->
  dchk k c (dec_idx1 (is_distbits s)) code_bits (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r = Some rf ->
  evt psegs (DECG X s c r0 r0 (DECODE_k k (is_distcode s) (dec_idx1 (is_distbits s)) code_bits (mkW s c r)) rf
               (is_distcode s) (dec_idx1 (is_distbits s)) code_bits PC_DIST_J1 (dist_Q1 X s)) ms.
Proof.
  induction k as [|k IH]; intros X s c r0 r rf [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms
    HL E9 E23 E26 E12 E13 E5 E6 E22 E16 E14 E17 E15 E29 E31 XO HREGS HPL HB0 HH0 Pin Pin1 RN CPO HB HD.
  { exfalso. exact (CK_short0 _ _ _ _ _ _ _ HD HB). }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
  subst x9 x23 x26 x12 x13 x5 x6 x22 x16 x14 x17 x15 x29 x31.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r0 r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r0 r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  set (p := is_distcode s) in *. set (n := is_distbits s) in *.
  pose proof (ones_range15 n RN) as RMK.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0].
  unfold PC_DIST_L1. ix_open XO.
  zs. br_cases K.
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (DC_dry k p (dec_idx1 n) code_bits s c r) by lia.
    do 9 zs. rewrite (zx32_small (ir_have r0)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply evt_done. right. exists r. split; [reflexivity|]. split; [exact HPL|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| first [assumption | symmetry; assumption | reflexivity]..].
  -
    pose proof (CK_pull _ _ _ _ _ _ _ _ HD HB ltac:(lia)) as HD'.
    rewrite (DC_pull k p (dec_idx1 n) code_bits s c r) by lia.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r0 r HREGS HB0 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7 & E8 & E9' & RH1).
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
      eapply (IH X s c r0 (pullr c r) rf);
        [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
        | exact XO | exact HREGS1 | exact HPL1 | exact HB0 | exact HH0 | exact Pin | exact Pin1 | exact RN | exact CPO | rewrite E6'; exact K3 | exact HD' ];
        subst p n; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
    +
      rewrite (DC_found k p (dec_idx1 n) code_bits s c (pullr c r)) by lia.
      destruct (CK_found _ _ _ _ _ _ _ _ HD' ltac:(lia)) as [_ ->].
      zs. apply evt_done. left. eexists (pullr c r), _. split; [reflexivity|]. split; [reflexivity|]. split; [lia|]. split; [exact RI1|].
      split; [exact HREGS1|]. split; [exact HPL1|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
      unfold dist_Q1. cbn [h12 h13 h14 h15 h16 h22 h27 h29 h31]. subst p n.
      repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
Qed.

Lemma dist_lvl1 : forall X s c r rf x8 x12 ms,
  ILOOP X (mkW s c r) PC_DIST x8 x12 ms -> ix_ok X -> REGS c r -> PATG X (mkW s c r) ->
  0 <= is_distbits s <= 15 -> cp_ofs_ok (is_distcode s) ->
  dchk 8 c (dec_idx1 (is_distbits s)) code_bits (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r = Some rf ->
  evt psegs (DECG X s c r r (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits (mkW s c r)) rf
               (is_distcode s) (dec_idx1 (is_distbits s)) code_bits PC_DIST_J1 (dist_Q1 X s)) ms.
Proof.
  intros X s c r rf x8 x12 ms HL XO HREGS HP RN CPO HD.
  destruct HL as (x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x27 & x28 & x30 & m & -> & HMEM). cbn [w_s w_c w_r] in *.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (REGS_hold64 c r HREGS) as RH64.
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST. open_isA GA.
  unfold PC_DIST. ix_open XO.
  set (p := is_distcode s) in *. set (n := is_distbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0]. pose proof (ones_range15 n RN) as RMK.
  do 5 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
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
    unfold dist_Q1. cbn [h12 h13 h14 h15 h16 h22 h27 h29 h31]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity.
    f_equal. rewrite Z.shiftl_mul_pow2 by lia. lia.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    do 4 zs.
    eapply (dist_loop1 8%nat X s c r r rf);
      [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h29 h31] ..
      | exact XO | exact HREGS | apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1 | exact RN | exact CPO | exact K' | exact HD ];
      subst e0 i0 p n; first [ reflexivity | f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia ].
Qed.

Definition PC_DIST_T : Z := 0x1e9d4.

Definition dist_QT (X : ictx) (here : Z) (rt : iregs) (B : Z) (q : iscrh) : Prop :=
  h6 q = wz (code_op here) /\ h16 q = wz (code_val here) /\ h14 q = wz (code_bits here) /\ h15 q = wz B
  /\ h13 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h27 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h9 q = wz (il_As (ix_L X) + 7160) /\ h29 q = wz 30 /\ h31 q = wz (-16180).

Lemma dist_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r1 q -> ix_ok X ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) = false ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 (bv_swrap 32 (is_back s)) q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO TWO.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E16 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x16 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  assert (K16 : 16 <= code_op e).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_gt in TWO. lia. }
  open_IST ST. open_isT GT. ix_open XO. unfold PC_DIST_J1.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  do 3 zs. br_true.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK.
  zs. rewrite EBK. zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT. cbn [h6 h9 h12 h13 h14 h15 h16 h22 h27 h29 h31]. repeat split; reflexivity.
Qed.

Definition PC_DIST_J2 : Z := 0x1e9a8.
Definition dist_Q2 (X : ictx) (s : inflate_state) (last : Z) (r2 : iregs) (q : iscrh) : Prop :=
  h17 q = wz (ir_have r2) /\ h5 q = wz (ir_bits r2) /\ h30 q = wz (il_NI (ix_L X) + ir_next r2) /\ h22 q = wz (ir_hold r2)
  /\ h7 q = wz (code_bits (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))))
  /\ h28 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx2 last (ir_hold r2))
  /\ h14 q = wz (code_bits last) /\ h9 q = wz (il_As (ix_L X) + 7160).

Definition PC_DIST_L2 : Z := 0x1e948.

Lemma dist_loop2 : forall k X s c r0 r1 r rf last q ms,
  ILOOPh X (mkW s c r0) PC_DIST_L2 q ms ->
  h12 q = wz (ir_have r1) -> h13 q = wz (ir_bits r1) -> h27 q = wz (il_NI (ix_L X) + ir_next r1) ->
  h17 q = wz (ir_have r) -> h29 q = wz (ir_bits r) -> h5 q = wz (ir_bits r) -> h31 q = wz (il_NI (ix_L X) + ir_next r) -> h22 q = wz (ir_hold r) ->
  h28 q = wz (cp_addr (ix_L X) (is_distcode s) + 4 * dec_idx2 last (ir_hold r)) ->
  h7 q = wz (code_bits (code_at s (is_distcode s) (dec_idx2 last (ir_hold r)))) ->
  h6 q = wz (Z.ones (code_bits last + code_op last)) -> h14 q = wz (code_bits last) -> h16 q = wz (code_val last) ->
  h15 q = wz (cp_addr (ix_L X) (is_distcode s)) -> h9 q = wz (il_As (ix_L X) + 7160) ->
  ix_ok X -> REGS c r -> pulled r1 r -> 0 <= ir_bits r1 -> 0 <= ir_have r1 < 2^31 -> ic_input c = ix_input X -> arr_len (ix_input X) < 2^31 ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_ret r1 = ir_ret r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 ->
  cp_ofs_ok (is_distcode s) -> 0 <= code_bits last -> 0 <= code_op last -> code_bits last + code_op last <= 31 -> 0 <= code_val last < 2^16 ->
  ir_bits r < dec_need2 last (code_at s (is_distcode s) (dec_idx2 last (ir_hold r))) ->
  dchk k c (dec_idx2 last) (dec_need2 last) (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r = Some rf ->
  evt psegs (DECG X s c r0 r1 (DECODE_k k (is_distcode s) (dec_idx2 last) (dec_need2 last) (mkW s c r)) rf
               (is_distcode s) (dec_idx2 last) (dec_need2 last) PC_DIST_J2 (dist_Q2 X s last)) ms.
Proof.
  induction k as [|k IH]; intros X s c r0 r1 r rf last [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms
    HL E12 E13 E27 E17 E29 E5 E31 E22 E28 E7 E6 E14 E16 E15 E9 XO HREGS HPL HB1 HH1 Pin Pin1 EI EO ER EP EL CPO RLB ROP K31 RVAL HB HD.
  { exfalso. exact (CK_short0 _ _ _ _ _ _ _ HD HB). }
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *.
  subst x12 x13 x27 x17 x29 x5 x31 x22 x28 x7 x6 x14 x16 x15 x9.
  pose proof HMEM as ((jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof (Rin (ir_next r)) as RBy. pose proof (REGS_hold64 c r HREGS) as RH64.
  pose proof (pulled_cursor r1 r HPL) as (CU1 & CU2 & CU3 & CU4 & CU5).
  destruct (pulled_eqs r1 r HPL) as (EQ1 & EQ2 & EQ3 & EQ4 & EQ5).
  assert (HAV : ir_have r < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST.
  set (p := is_distcode s) in *.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI0 RN0].
  unfold PC_DIST_L2. ix_open XO.
  zs. br_cases K.
  -
    assert (H0 : ir_have r = 0) by lia.
    rewrite (DC_dry k p (dec_idx2 last) (dec_need2 last) s c r) by lia.
    do 8 zs. rewrite (zx32_small (ir_have r1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    apply evt_done. right. exists r. split; [reflexivity|]. split; [exact HPL|].
    eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| congruence..].
  -
    pose proof (CK_pull _ _ _ _ _ _ _ _ HD HB ltac:(lia)) as HD'.
    rewrite (DC_pull k p (dec_idx2 last) (dec_need2 last) s c r) by lia.
    assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
    destruct (pull_step c r1 r HREGS HB1 HPL ltac:(lia) ltac:(lia)) as (HREGS1 & HPL1 & E1 & E2 & E5' & E6' & E3 & E4 & E7' & E8 & E9' & RH1).
    assert (RH1' : 0 <= ir_hold (pullr c r) < 2^64).
    { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH1)|]. apply Z.pow_le_mono_r; lia. }
    apply (id : _ -> hide _) in RH1.
    pose proof (u8ro_read psegs _ _ _ (ir_next r) _ (wa (il_NI (ix_L X) + ir_next r)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
    zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
    replace (arr_get (ic_input c) (ir_next r) * 2 ^ ir_bits r + ir_hold r) with (ir_hold (pullr c r)) by lia.
    set (h2 := ir_hold (pullr c r)) in *.
    pose proof (land_ones_le h2 (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
    assert (EI3 : (Z.land h2 mk2 ≫ code_bits last) + code_val last = dec_idx2 last h2) by (subst mk2; rewrite dec_idx2_clang by lia; reflexivity).
    zs. set (hm3 := Z.land h2 mk2) in *.
    pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
    zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
    do 3 zs. rewrite (zext32_x4 (sh3 + code_val last)) by lia. rewrite EI3.
    destruct (CK_range _ _ _ _ _ _ _ _ HD') as [RI3 RN3]. fold h2 in RI3, RN3.
    set (i3 := dec_idx2 last h2) in *. set (e3 := code_at s p i3) in *. pose proof (code_bits_range e3) as RB3.
    assert (EN3 : dec_need2 last e3 = code_bits last + code_bits e3) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
    rewrite EN3 in *.
    zs.
    pose proof (code_rd_bits m (ix_L X) s p i3 (wa (cp_addr (ix_L X) p + 4 * i3 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
    fold e3 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e3)) by exact RB3. clear RD.
    do 7 zs. br_cases K3.
    +
      assert (K3' : ir_bits (pullr c r) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r))))) by (fold h2; fold i3; fold e3; rewrite EN3; lia).
      eapply (IH X s c r0 r1 (pullr c r) rf last);
        [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h27 h28 h29 h31] ..
        | exact XO | exact HREGS1 | exact HPL1 | exact HB1 | exact HH1 | exact Pin | exact Pin1 | exact EI | exact EO | exact ER | exact EP | exact EL
        | exact CPO | exact RLB | exact ROP | exact K31 | exact RVAL | exact K3' | exact HD' ];
        subst e3 i3 sh3 hm3 h2 mk2 p; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; lia ].
    +
      assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r)))) <= ir_bits (pullr c r)) by (fold h2; fold i3; fold e3; rewrite EN3; lia).
      rewrite (DC_found k p (dec_idx2 last) (dec_need2 last) s c (pullr c r)) by exact K3'.
      destruct (CK_found _ _ _ _ _ _ _ _ HD' K3') as [_ ->].
      zs. apply evt_done. left. eexists (pullr c r), _. split; [reflexivity|]. split; [reflexivity|]. split; [exact K3'|]. split; [subst i3 h2; exact RI3|].
      split; [exact HREGS1|]. split; [exact HPL1|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
      unfold dist_Q2. cbn [h5 h7 h9 h14 h17 h22 h28 h30]. subst e3 i3 sh3 hm3 h2 mk2 p.
      repeat split; first [ reflexivity | rewrite ?E1, ?E2, ?E6'; ireg | f_equal; lia ].
Qed.

Lemma dist_lvl2 : forall X s c r0 r1 rf q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r1 q -> ix_ok X -> PATG X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  REGS c r1 ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  forall last, last = code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) ->
  dist_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dchk 8 c (dec_idx2 last) (dec_need2 last) (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r1 = Some rf ->
  evt psegs (DECG X s c r0 r1 (DECODE_k 8 (is_distcode s) (dec_idx2 last) (dec_need2 last) (mkW s c r1)) rf
               (is_distcode s) (dec_idx2 last) (dec_need2 last) PC_DIST_J2 (dist_Q2 X s last)) ms.
Proof.
  intros X s c r0 r1 rf [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         HREGS RI CPO last ELAST TWO KB K31 HD.
  destruct HQ as (E12 & E13 & E27 & E22 & E14 & E16 & E15 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x12 x13 x27 x22 x14 x16 x15 x29 x31.
  iarm_openh_keep HL HMEM.
  pose proof HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS.
  assert (K15 : code_op last <= 15).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_le in TWO. exact TWO. }
  pose proof (REGS_hold64 c r1 HREGS) as RH64.
  assert (HAV : ir_have r1 < 2^31) by (rewrite Pin in Rnh; lia).
  apply (id : _ -> hide _) in RH.
  open_IST ST. ix_open XO. unfold PC_DIST_J1.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. cbv beta. rewrite (bv8_small (code_op last)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  rewrite <- ELAST in RD. zs. rewrite (zx16_small (code_val last)) by exact RVAL. clear RD.
  do 3 zs. br_false.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 4 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  do 3 zs. rewrite (zext32_x4 (sh + code_val last)) by lia.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (subst sh hm mk2; rewrite dec_idx2_clang by lia; reflexivity).
  rewrite EI2. destruct (CK_range _ _ _ _ _ _ _ _ HD) as [RI2 RN2].
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
  zs.
  pose proof (code_rd_bits m (ix_L X) s p i2 (wa (cp_addr (ix_L X) p + 4 * i2 + 1)) MI Gc CPO ltac:(lia) eq_refl) as RD.
  fold e2 in RD. zs. cbv beta. rewrite (bv8_small (code_bits e2)) by exact RB2. clear RD.
  do 2 zs. br_cases K.
  -
    assert (K' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1))) <= ir_bits r1) by (fold i2; fold e2; rewrite EN2; lia).
    rewrite (DC_found 8 p (dec_idx2 last) (dec_need2 last) s c r1) by exact K'.
    destruct (CK_found _ _ _ _ _ _ _ _ HD K') as [_ ->].
    do 3 zs. apply evt_done. left. eexists r1, _. split; [reflexivity|]. split; [reflexivity|]. split; [exact K'|]. split; [exact RI2|].
    split; [exact HREGS|]. split; [apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)]|].
    split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q2. cbn [h5 h7 h9 h14 h17 h22 h28 h30]. fold p. fold i2. fold e2. repeat split; reflexivity.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; exact K).
    do 4 zs.
    eapply (dist_loop2 8%nat X s c r0 r1 r1 rf last);
      [ eapply ILOOPh_intro; ired; [ireg .. | exact HMEM] | cbn [h5 h6 h7 h9 h12 h13 h14 h15 h16 h17 h22 h27 h28 h29 h31] ..
      | exact XO | exact HREGS | apply pulled_refl; [exact Rh| unfold hide in RH; exact (conj RB RH)] | lia | lia | exact Pin | exact Pin1
      | exact EI | exact EO | exact ER | exact EP | exact EL | exact CPO | lia | lia | exact K31 | exact RVAL | exact K' | exact HD ];
      subst e2 i2 sh hm mk2 p i; first [ reflexivity | f_equal; lia ].
Qed.

Lemma dist_j2 : forall X s c r0 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J2 q ms -> dist_Q2 X s last r2 q -> ix_ok X ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 ->
  evt psegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last))
                                              (bv_swrap 32 (is_back s) + code_bits last) q') ms.
Proof.
  intros X s c r0 r2 last [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO RI CPO RB RH.
  destruct HQ as (E17 & E5 & E30 & E22 & E7 & E28 & E14 & E9).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x17 x5 x30 x22 x7 x28 x14 x9.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_val_range e) as RVAL. pose proof (code_bits_range e) as RBITS.
  pose proof (code_bits_range last) as RLB.
  open_IST ST. open_isT GT. ix_open XO. unfold PC_DIST_J2.
  pose proof (bv_swrap32_range (is_back s)) as RBK. pose proof (sx32_wz_u (is_back s)) as EBK.
  zs. rewrite EBK.
  pose proof (code_rd_op m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. cbv beta. rewrite (bv8_small (code_op e)) by exact ROP. clear RD.
  pose proof (code_rd_val m (ix_L X) s p i (wa (cp_addr (ix_L X) p + 4 * i + 2)) MI Gc CPO RI eq_refl) as RD.
  fold e in RD. zs. rewrite (zx16_small (code_val e)) by exact RVAL. clear RD.
  do 8 zs. rewrite (land63_small (code_bits last)) by lia.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT, ddrop. cbn [h6 h9 h12 h13 h14 h15 h16 h22 h27 h29 h31 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
  repeat split; try reflexivity; ireg.
Qed.
