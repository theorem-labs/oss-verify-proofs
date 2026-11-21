(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_ikit Z_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_c_tab Z_infl_a_match Z_infl_a_distext.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST RefInflateSafeOK RefInflateSafeOK2 InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition DECJ (X : ictx) (s : inflate_state) (c : icall) (r0 r : iregs) (p : codeptr) (index need : Z -> Z) (pcj : Z)
    (Q : iregs -> iscrh -> Prop) : machine_state -> Prop :=
  fun ms' =>
    (exists r1 q, DECODE_k 8 p index need (mkW s c r) = ARun (code_at s p (index (ir_hold r1))) (mkW s c r1)
                  /\ dchk 8 c index need (ctab_size p) (code_at s p) r = Some r1
                  /\ need (code_at s p (index (ir_hold r1))) <= ir_bits r1
                  /\ 0 <= index (ir_hold r1) < ctab_size p
                  /\ (r1 = r \/ (r1 = pullr c r /\ ir_have r = 1 /\ ir_bits r <= 31))
                  /\ ILOOPh X (mkW s c r0) pcj q ms' /\ Q r1 q)
    \/ (exists r1, DECODE_k 8 p index need (mkW s c r) = ALeave (mkW s c r1) /\ (r1 = r \/ (r1 = pullr c r /\ ir_have r = 1 /\ ir_bits r <= 31)) /\ ILEAVE X (mkW s c r1) ms').
Definition PC_DIST_L1 : Z := 0x210dc.
Definition PC_DIST_J1 : Z := 0x2115c.
Definition dist_Q1 (X : ictx) (s : inflate_state) (r : iregs) (r1 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) in
  h30 q = wz (code_w e) /\ h28 q = wz (code_bits e) /\ h7 q = wz (code_w e ≫ 8)
  /\ h15 q = wz (ir_bits r1) /\ h14 q = wz (ir_bits r1) /\ h22 q = wz (ir_hold r1)
  /\ h12 q = wz (ir_have r1) /\ h16 q = wz (ir_have r1) /\ h17 q = wz (8 * ir_have r1)
  /\ h5 q = wz (il_NI (ix_L X) + ir_next r1) /\ h6 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h11 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h13 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2).
Definition DE (X : ictx) (r : iregs) (q : iscrh) : Prop :=
  h9 q = wz (il_NO (ix_L X) + ir_put r) /\ h10 q = wz (-2) /\ h18 q = wz (ir_bits r) /\ h22 q = wz (ir_hold r)
  /\ h24 q = wz (ir_have r) /\ h25 q = wz (il_NI (ix_L X) + ir_next r).
Lemma DE_of_hhome : forall X r q, hhome X r q -> DE X r q.
Proof. intros X r q (E9 & E10 & _ & _ & E18 & E22 & E24 & E25). repeat split; assumption. Qed.
Lemma dist_lvl1 : forall X s c r q ms,
  ILOOPh X (mkW s c r) PC_DIST q ms -> DE X r q -> ix_ok X -> REGS c r -> PATI X (mkW s c r) ->
  0 <= is_distbits s <= 15 -> cp_ofs_ok (is_distcode s) ->
  dlvl c s (is_distcode s) (dec_idx1 (is_distbits s)) code_bits r ->
  evt usegs (DECJ X s c r r (is_distcode s) (dec_idx1 (is_distbits s)) code_bits PC_DIST_J1 (dist_Q1 X s r)) ms.
Proof.
  intros X s c r [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL
         (E9 & E10 & E18 & E22 & E24 & E25) XO HREGS HP RN CPO DL.
  destruct HL as (m & -> & HMEM). cbn [w_s w_c w_r h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x9 x10 x18 x22 x24 x25.
  pose proof HMEM as ((j0 & jf & FRM) & _ & [_ ST] & IN & _ & MI & _). unfold iin in IN. unfold iframe_cells in FRM. cbn [w_r w_s] in *.
  destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & [RB RH] & Rin & Rli & Rlo).
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof (Rin (ir_next r)) as RBy.
  assert (HAV : ir_have r <= 1) by (rewrite Pin in Rnh; lia).
  assert (RH64 : 0 <= ir_hold r < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. open_isA GA.
  unfold PC_DIST. ix_open XO.
  set (p := is_distcode s) in *. set (n := is_distbits s) in *.
  pose proof (dec_idx1_land n (ir_hold r) ltac:(lia) RN) as EI0. pose proof (dec_idx1_range n (ir_hold r) ltac:(lia) RN) as RI0'.
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI0. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN0. pose proof (ones_range15 n RN) as RMK.
  do 2 zs. gF. do 4 zs. rewrite clang_mask32 by lia. zs. rewrite EI0.
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
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i0; fold e0; lia)) as [ED EC].
    apply evt_done. left. eexists r, _. split; [exact ED|]. split; [exact EC|]. split; [fold i0; fold e0; lia|]. split; [exact RI0|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h22 h28 h30]. fold p. fold n. fold i0. fold e0. repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r < code_bits (code_at s p (dec_idx1 n (ir_hold r)))) by (fold i0; fold e0; exact K).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 10 zs. rewrite H0. change (0 ≪ 3) with 0. change (Z.land 0 4294967295) with 0. rewrite !Z.add_0_r.
      apply evt_done. right. exists r. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| reflexivity..].
    +
      assert (H1 : ir_have r = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI1 RN1].
      assert (NXT : 0 <= ir_next r < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
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
      zs. rewrite (Z.shiftl_mul_pow2 i1 2) by lia. change (2^2) with 4. zs. gF.
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
        unfold hide in RH. unfold dist_Q1. cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h22 h28 h30]. fold p. fold n. fold h1. fold i1. fold e1.
        repeat split; try reflexivity; try (pullr_rw c r; ireg).
      *
        assert (K3' : ir_bits (pullr c r) < code_bits (code_at s p (dec_idx1 n (ir_hold (pullr c r))))) by (fold h1; fold i1; fold e1; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 10 zs. rewrite H1. change (1 ≪ 3) with 8. change (Z.land 1 4294967295) with 1.
        apply evt_done. right. exists (pullr c r). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e1 i1 h1. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| reflexivity..]]; pullr_rw c r; ireg.
Qed.
Definition PC_DIST_T : Z := 0x21290.
Definition dist_QT (X : ictx) (here : Z) (rt : iregs) (r0 : iregs) (q : iscrh) : Prop :=
  h30 q = wz (code_w here) /\ h29 q = wz (code_op here) /\ h20 q = wz (code_bits here) /\ h21 q = wz (code_w here ≫ 8)
  /\ h14 q = wz (ir_bits rt) /\ h22 q = wz (ir_hold rt) /\ h12 q = wz (ir_have rt) /\ h25 q = wz (il_NI (ix_L X) + ir_next rt)
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r0) /\ h10 q = wz (-2).
Lemma dist_direct : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r0 r1 q -> ix_ok X ->
  dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) = false ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW s c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 r0 q') ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO TWO.
  destruct HQ as (E30 & E28 & E7 & E15 & E14 & E22 & E12 & E16 & E17 & E5 & E6 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *. subst.
  iarm_openh_keep HL HMEM.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_w_range e) as RW.
  assert (K16 : 16 <= code_op e).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_gt in TWO. lia. }
  ix_open XO. unfold PC_DIST_J1.
  zs. rewrite code_w_op. do 2 zs. br_true. do 4 zs.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
  unfold dist_QT. cbn [h9 h10 h12 h14 h20 h21 h22 h25 h29 h30]. repeat split; reflexivity.
Qed.
Definition PC_DIST_L2 : Z := 0x211cc.
Definition PC_DIST_J2 : Z := 0x21268.
Definition dist_Q2 (X : ictx) (s : inflate_state) (last : Z) (r1 r2 : iregs) (q : iscrh) : Prop :=
  let e := code_at s (is_distcode s) (dec_idx2 last (ir_hold r2)) in
  h30 q = wz (code_w e) /\ h21 q = wz (code_w e ≫ 8) /\ h20 q = wz (code_bits e) /\ h24 q = wz (code_bits e + code_bits last)
  /\ h19 q = wz (ir_bits r2) /\ h22 q = wz (ir_hold r2) /\ h12 q = wz (ir_have r2) /\ h25 q = wz (il_NI (ix_L X) + ir_next r2)
  /\ h14 q = wz (ir_bits r1) /\ h15 q = wz (ir_bits r1) /\ h16 q = wz (ir_have r1) /\ h17 q = wz (8 * ir_have r1) /\ h5 q = wz (il_NI (ix_L X) + ir_next r1)
  /\ h18 q = wz (code_bits last + ir_bits r1 - ir_bits r2)
  /\ h28 q = wz (code_bits last) /\ h29 q = wz (code_val last) /\ h7 q = wz (code_w last ≫ 8)
  /\ h11 q = wz (cp_addr (ix_L X) (is_distcode s)) /\ h13 q = wz 1
  /\ h9 q = wz (il_NO (ix_L X) + ir_put r1) /\ h10 q = wz (-2).
Lemma dist_lvl2 : forall X s c r0 r1 q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J1 q ms -> dist_Q1 X s r0 r1 q -> ix_ok X -> PATI X (mkW s c r0) ->
  ir_in r1 = ir_in r0 -> ir_out r1 = ir_out r0 -> ir_put r1 = ir_put r0 -> ir_left r1 = ir_left r0 -> ir_ret r1 = ir_ret r0 ->
  0 <= ir_have r1 <= 1 -> 0 <= ir_next r1 -> ir_next r1 + ir_have r1 = arr_len (ic_input c) -> 0 <= ir_bits r1 <= 63 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  (forall i, 0 <= arr_get (ic_input c) i < 256) ->
  0 <= dec_idx1 (is_distbits s) (ir_hold r1) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  forall last, last = code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)) ->
  dist_two (code_op last) = true -> code_bits last <= ir_bits r1 -> code_bits last + code_op last <= 31 ->
  dlvl c s (is_distcode s) (dec_idx2 last) (dec_need2 last) r1 ->
  evt usegs (DECJ X s c r0 r1 (is_distcode s) (dec_idx2 last) (dec_need2 last) PC_DIST_J2 (dist_Q2 X s last r1)) ms.
Proof.
  intros X s c r0 r1 [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP EI EO EP EL ER
         RHV RNX RNH RB RH Rin RI CPO last ELAST TWO KB K31 DL.
  destruct HQ as (E30 & E28 & E7 & E15 & E14 & E22 & E12 & E16 & E17 & E5 & E6 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x30 x28 x7 x15 x14 x22 x12 x16 x17 x5 x6 x11 x13 x9 x10.
  iarm_openh_keep HL HMEM.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx1 (is_distbits s) (ir_hold r1)) in *. rewrite <- ELAST in *.
  pose proof (code_op_range last) as ROP. pose proof (code_val_range last) as RVAL. pose proof (code_bits_range last) as RBITS. pose proof (code_w_range last) as RWL.
  assert (K15 : code_op last <= 15).
  { unfold dist_two in TWO. rewrite (land240_le15 _ ROP) in TWO. apply Z.leb_le in TWO. exact TWO. }
  assert (RH64 : 0 <= ir_hold r1 < 2^64).
  { split; [lia|]. eapply Z.lt_le_trans; [exact (proj2 RH)|]. apply Z.pow_le_mono_r; lia. }
  pose proof (Rin (ir_next r1)) as RBy. apply (id : _ -> hide _) in RH. clear Rin.
  open_IST ST. ix_open XO. unfold PC_DIST_J1.
  zs. rewrite code_w_op. do 2 zs. br_false.
  do 2 zs. rewrite code_w_ge000 by lia. gF.
  zs. rewrite code_w_land15, (land15_small (code_op last)) by lia. do 2 zs. gF.
  zs. rewrite code_w_val.
  pose proof (ones_range31 (code_bits last + code_op last) ltac:(lia)) as RMK2.
  pose proof (land_ones_le (ir_hold r1) (code_bits last + code_op last) ltac:(lia)) as RHM.
  do 3 zs. rewrite clang_mask32 by lia. set (mk2 := Z.ones (code_bits last + code_op last)) in *.
  zs. set (hm := Z.land (ir_hold r1) mk2) in *.
  pose proof (shiftr_le hm (code_bits last) ltac:(lia) ltac:(lia)) as RSH.
  zs. rewrite (srlw_small hm (code_bits last)) by lia. set (sh := hm ≫ code_bits last) in *.
  zs.
  assert (EI2 : sh + code_val last = dec_idx2 last (ir_hold r1)) by (rewrite dec_idx2_clang by lia; reflexivity).
  pose proof (dl_i0 _ _ _ _ _ _ DL) as RI2. pose proof (dl_n0 _ _ _ _ _ _ DL) as RN2.
  do 2 zs. rewrite (zext32_x4 (sh + code_val last)) by lia. rewrite EI2.
  set (i2 := dec_idx2 last (ir_hold r1)) in *. set (e2 := code_at s p i2) in *. pose proof (code_bits_range e2) as RB2. pose proof (code_w_range e2) as RW2.
  assert (EN2 : dec_need2 last e2 = code_bits last + code_bits e2) by (unfold dec_need2; rewrite wrap32_id by lia; reflexivity).
  rewrite EN2 in *.
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
    destruct (dl_found0 _ _ _ _ _ _ DL ltac:(fold i2; fold e2; rewrite EN2; lia)) as [ED EC].
    apply evt_done. left. eexists r1, _. split; [exact ED|]. split; [exact EC|]. split; [fold i2; fold e2; rewrite EN2; lia|]. split; [exact RI2|].
    split; [left; reflexivity|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
    unfold dist_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h28 h29 h30 h31]. fold p. fold i2. fold e2.
    repeat split; try reflexivity; ireg.
  - assert (K' : ir_bits r1 < dec_need2 last (code_at s p (dec_idx2 last (ir_hold r1)))) by (fold i2; fold e2; rewrite EN2; lia).
    zstep. br_cases K2.
    +
      assert (H0 : ir_have r1 = 0) by lia.
      pose proof (dl_dry0 _ _ _ _ _ _ DL K' H0) as ED.
      do 7 zs. rewrite H0. rewrite ?Z.add_0_r, ?Z.mul_0_r, ?Z.add_0_l.
      apply evt_done. right. exists r1. split; [exact ED|]. split; [left; reflexivity|].
      eapply ILEAVE_intro; ired; [ireg .. |]. eapply IMEML_of_IMEM; [exact HMEM| assumption..].
    +
      assert (H1 : ir_have r1 = 1) by lia.
      destruct (dl_i1 _ _ _ _ _ _ DL K' H1) as [RI3 RN3].
      assert (NXT : 0 <= ir_next r1 < arr_len (ix_input X)) by (rewrite <- Pin; lia).
      do 2 zs. gF. zs. gF.
      pose proof (u8ro_read usegs _ _ _ (ir_next r1) _ (wa (il_NI (ix_L X) + ir_next r1)) IN (av8_nth _ _ _ NXT) ltac:(lia) eq_refl) as RD.
      zs. clear RD. do 2 zs. rewrite <- Pin. rewrite !pull_shift by lia.
      assert (EH2 : arr_get (ic_input c) (ir_next r1) * 2 ^ ir_bits r1 + ir_hold r1 = ir_hold (pullr c r1)).
      { unfold hide in RH. rewrite pullr_hold by (first [assumption | lia]). lia. }
      pose proof (pull_hold_range (arr_get (ic_input c) (ir_next r1)) (ir_bits r1) (ir_hold r1) RBy ltac:(lia) RH) as PR.
      assert (RH2 : 0 <= ir_hold (pullr c r1) < 2^64).
      { rewrite <- EH2. split; [lia|]. eapply Z.lt_le_trans; [rewrite Z.add_comm; exact (proj2 PR)|]. apply Z.pow_le_mono_r; lia. }
      rewrite EH2. clear PR EH2.
      pose proof (land_ones_le (ir_hold (pullr c r1)) (code_bits last + code_op last) ltac:(lia)) as RHM3. fold mk2 in RHM3.
      assert (EI3 : (Z.land (ir_hold (pullr c r1)) mk2 ≫ code_bits last) + code_val last = dec_idx2 last (ir_hold (pullr c r1))) by (rewrite dec_idx2_clang by lia; reflexivity).
      set (h2 := ir_hold (pullr c r1)) in *.
      zs. set (hm3 := Z.land h2 mk2) in *.
      pose proof (shiftr_le hm3 (code_bits last) ltac:(lia) ltac:(lia)) as RSH3.
      zs. rewrite (srlw_small hm3 (code_bits last)) by lia. set (sh3 := hm3 ≫ code_bits last) in *.
      zs. rewrite EI3.
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
      * assert (K3' : dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1)))) <= ir_bits (pullr c r1)) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        destruct (dl_found1 _ _ _ _ _ _ DL K' H1 K3') as [ED EC].
        apply evt_done. left. eexists (pullr c r1), _. split; [exact ED|]. split; [exact EC|]. split; [exact K3'|]. split; [exact RI3|].
        split; [right; split; [reflexivity| split; [exact H1| lia]]|]. split; [eapply ILOOPh_intro; ired; [ireg .. | exact HMEM]|].
        unfold hide in RH. unfold dist_Q2. cbn [h5 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h28 h29 h30 h31]. fold p. fold h2. fold i3. fold e3.
        repeat split; try reflexivity; try (pullr_rw c r1; ireg).
      *
        assert (K3' : ir_bits (pullr c r1) < dec_need2 last (code_at s p (dec_idx2 last (ir_hold (pullr c r1))))) by (fold h2; fold i3; fold e3; rewrite EN3; rewrite pullr_bits by lia; lia).
        pose proof (dl_dry1 _ _ _ _ _ _ DL K' H1 K3') as ED.
        zstep. br_true. do 7 zs. rewrite H1.
        apply evt_done. right. exists (pullr c r1). split; [exact ED|]. split; [right; split; [reflexivity| split; [exact H1| lia]]|].
        unfold hide in RH. subst e3 i3 sh3 hm3 h2. eapply ILEAVE_intro; ired; [ .. | eapply IMEML_of_IMEM; [exact HMEM| assumption..]]; pullr_rw c r1; ireg.
Qed.
Lemma dist_j2 : forall X s c r0 r1 r2 last q ms,
  ILOOPh X (mkW s c r0) PC_DIST_J2 q ms -> dist_Q2 X s last r1 r2 q -> ix_ok X -> PATI X (mkW s c r0) ->
  0 <= dec_idx2 last (ir_hold r2) < ctab_size (is_distcode s) -> cp_ofs_ok (is_distcode s) ->
  code_bits last <= ir_bits r2 <= 63 -> 0 <= ir_hold r2 < 2^64 -> 0 <= ir_bits r1 <= 63 -> code_bits last + code_op last <= 31 ->
  -1 <= is_back s <= 525 -> 0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) -> ir_put r1 = ir_put r0 ->
  evt usegs (fun ms' => exists q', ILOOPh X (mkW (addback s (code_bits last)) c r0) PC_DIST_T q' ms'
                                   /\ dist_QT X (code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) (ddrop r2 (code_bits last)) r0 q') ms.
Proof.
  intros X s c r0 r1 r2 last [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO HP RI CPO RB RH RB1 K31 BK RPUT EP.
  destruct HQ as (E30 & E21 & E20 & E23 & E19 & E22 & E12 & E25 & E14 & E15 & E16 & E17 & E5 & E18 & E28 & E29 & E7 & E11 & E13 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x30 x21 x20 x24 x19 x22 x12 x25 x14 x15 x16 x17 x5 x18 x28 x29 x7 x11 x13 x9 x10.
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  set (p := is_distcode s) in *. set (i := dec_idx2 last (ir_hold r2)) in *. set (e := code_at s p i) in *.
  pose proof (code_op_range e) as ROP. pose proof (code_bits_range e) as RBITS. pose proof (code_w_range e) as RWE.
  pose proof (code_bits_range last) as RLB. pose proof (code_op_range last) as RLO. pose proof (code_w_range last) as RWL.
  ix_open XO. unfold PC_DIST_J2.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r0) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT.
  pose proof (munch_refl [(ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168); (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  do 4 zs. rewrite addw_land64 by lia. gF.
  zs. rewrite subw_land64 by lia. zs. rewrite code_w_g31 by lia. zs. rewrite code_w_op. zs. rewrite (land63_small (code_bits last)) by lia.
  zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |]|].
  - unfold addback. apply IMEM_intro; inorm;
    [ exists j0, jf; exact FRM | exact STK | exact ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA
                          | unfold isT, isT_cells; exists padT; inorm; close_cells GT; apply le4_swrap32_r
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - unfold dist_QT, ddrop. cbn [h9 h10 h12 h14 h20 h21 h22 h25 h29 h30 ir_bits ir_hold ir_have ir_next irset_bits irset_hold].
    rewrite EP. repeat split; try reflexivity. all: rewrite ?wrap32_id by lia; f_equal; lia.
Qed.
