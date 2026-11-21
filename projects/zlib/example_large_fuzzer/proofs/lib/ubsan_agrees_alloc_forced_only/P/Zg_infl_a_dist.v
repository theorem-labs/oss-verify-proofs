(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Zg_infl_defs Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_defs Z_infl_c_pure Z_infl_c_tab Zg_infl_t_iface Zg_infl_c_kit Zg_infl_a_dist1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST RefInflateSafeOK RefInflateSafeOK2 InffastMem RefInflateSafeH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma land64_cases : forall op, 0 <= op < 256 -> 0 <= Z.land op 64 <= 64.
Proof.
  intros op Hop.
  assert (H : forallb (fun i : nat => (0 <=? Z.land (Z.of_nat i) 64) && (Z.land (Z.of_nat i) 64 <=? 64)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
Lemma land15_range : forall op, 0 <= Z.land op 15 < 16.
Proof. intros op. change 15 with (Z.ones 4). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma land32_cases : forall op, 0 <= op < 256 -> 0 <= Z.land op 32 <= 32.
Proof.
  intros op Hop.
  assert (H : forallb (fun i : nat => (0 <=? Z.land (Z.of_nat i) 32) && (Z.land (Z.of_nat i) 32 <=? 32)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat op) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.

Lemma le4_back_add2 : forall b l h, le4 (wz (bv_swrap 32 b + l + h)) = le4 (wz (swrap32 (swrap32 (b + l) + h))).
Proof.
  intros b l h. apply le4_wz_mod. rewrite Z_to_bv_unsigned. unfold swrap32, two31. rewrite !wrap32_mod.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.

Definition dt_sb (s : inflate_state) (Bm : Z) : inflate_state := iset_back s Bm.
Definition dt_bad (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_back s Bm) BAD) (icset_msg c MSG_invalid_distance_code) (ddrop rt (code_bits here)).
Definition dt_ok (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bm : Z) : iw :=
  mkW (iset_mode (iset_extra (iset_offset (iset_back s Bm) (code_val here)) (Z.land (code_op here) 15)) DISTEXT) c (ddrop rt (code_bits here)).

Lemma dist_tail_walk : forall X s c r0 rt here B Bm q ms,
  ILOOPh X (mkW s c r0) PC_DIST_T q ms -> dist_QT X here rt B q -> ix_ok X -> PATG X (mkW s c r0) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  le4 (wz (B + code_bits here)) = le4 (wz Bm) -> - 2^31 <= B < 2^31 + 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt psegs (fun ms' =>
     if negb (Z.land (code_op here) 64 =? 0) then exists x8, ILOOP X (dt_bad s c here rt Bm) PC_DISPATCH x8 (wz BAD) ms'
     else exists q', ILOOPg X (dt_ok s c here rt Bm) PC_DISTEXT_E q' ms' /\ sc13 q' = wz (Z.land (code_op here) 15)
                     /\ sc26 q' = wz (il_NI (ix_L X) + ir_next rt)) ms.
Proof.
  intros X s c r0 rt here B Bm [x5 x6 x7 x8 x9 x12 x13 x14 x15 x16 x17 x22 x23 x26 x27 x28 x29 x30 x31] ms HL HQ XO HP
         EI EO ER EP EL HB RBv RB RH RHV RNX RPUT.
  destruct HQ as (E6 & E16 & E14 & E15 & E13 & E22 & E12 & E27 & E9 & E29 & E31).
  cbn [h5 h6 h7 h8 h9 h12 h13 h14 h15 h16 h17 h22 h23 h26 h27 h28 h29 h30 h31] in *. subst x6 x16 x14 x15 x13 x22 x12 x27 x9 x29 x31.
  apply (ILOOPh_regs X s c r0 rt) in HL; [|assumption..].
  iarm_openh HL.
  pose proof HP as (_ & _ & _ & _ & _ & Pwin & Pin & Pin1 & Pout & Pout1 & _). cbn [w_s w_c w_r] in *.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS.
  ix_open XO. unfold PC_DIST_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl psegs m) as WMf.
  pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  do 4 zs. rewrite (land63_small (code_bits here)) by lia.
  do 2 zs. br_cases K.
  -
    replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
    do 8 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. eapply ILOOP_intro; unfold dt_bad, ddrop; ired; [ireg .. |].
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; exact HB
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
  - replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
    do 7 zs.
    itr_groups MUf WMf.
    apply evt_done. eexists. split; [eapply ILOOPg_intro; unfold dt_ok, ddrop; ired; [ireg .. |]|cbn [sc13 sc26]; split; reflexivity].
    apply IMEM_intro; inorm;
    [ exists jf; exact FRM | exact STK
    | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
    | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT; exact HB
                          | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
    | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.

Lemma cpok_ofs_ok : forall ty codes p root, cpok ty codes p root -> cp_ofs_ok p.
Proof. intros ty codes [ofs| |] root H; cbn in *; [exact (proj1 H)| exact I| exact I]. Qed.

Section Dist.
Hypothesis DISTEXT_CORE : distext_core_stmt.

Lemma dist_fin : forall X s c r rt here sb B q ms,
  ILOOPh X (mkW s c r) PC_DIST_T q ms -> dist_QT X here rt B q -> ix_ok X -> WINV (mkW s c r) -> PATG X (mkW s c r) -> is_mode s = DIST ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  (addback sb (code_bits here) = iset_back s (swrap32 (is_back sb + code_bits here))) ->
  le4 (wz (B + code_bits here)) = le4 (wz (swrap32 (is_back sb + code_bits here))) -> - 2^31 <= B < 2^31 + 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  dist_next (mkW s c r) = dist_tailnext s c here rt sb ->
  evt psegs (fun ms' => IPOST X (dist_tail c here rt sb) ms' /\ PATG X (wof (dist_tail c here rt sb))) ms.
Proof.
  intros X s c r rt here sb B q ms HL HQ XO HW HP HM EI EO ER EP EL ESB HB RBv RB RH RHV RNX HN.
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (_ & _ & _ & Rp & Rl & Rpl & _).
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  eapply evt_cut; [exact (dist_tail_walk X s c r rt here B _ q ms HL HQ XO HP EI EO ER EP EL HB RBv RB RH RHV RNX ltac:(lia))|].
  intros ms1 H1. unfold dist_tail. unfold dist_tailnext, dt_s in HN. cbv zeta. rewrite ESB. unfold dt_bad, dt_ok in H1.
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  - destruct H1 as (x8' & H1). apply evt_done. split; [cbn [IPOST]; exists x8'; exact H1|]. cbn [wof].
    eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr.
  - destruct H1 as (q' & H1 & E13 & E26).
    destruct (dist_next_WINV _ _ HW HM HN) as [HW3 HM3].
    refine (DISTEXT_CORE X _ q' ms1 H1 E13 E26 XO HW3 _ HM3).
    eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold DISTEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity|]. exact Pisr.
Qed.

Lemma ddrop_facts' : forall r n, 0 <= n <= ir_bits r -> ir_bits r <= 63 -> 0 <= ir_hold r < 2^64 ->
  ir_in (ddrop r n) = ir_in r /\ ir_out (ddrop r n) = ir_out r /\ ir_ret (ddrop r n) = ir_ret r /\ ir_put (ddrop r n) = ir_put r
  /\ ir_left (ddrop r n) = ir_left r /\ ir_bits (ddrop r n) = ir_bits r - n /\ 0 <= ir_hold (ddrop r n) < 2^64
  /\ ir_have (ddrop r n) = ir_have r /\ ir_next (ddrop r n) = ir_next r.
Proof.
  intros r n Hn Hb Hh. unfold ddrop. destruct r; cbn in *. rewrite wrap32_id by lia.
  pose proof (shiftr_le ir_hold n ltac:(lia) ltac:(lia)). repeat split; try reflexivity; lia.
Qed.

Lemma dist_core : forall X w x8 x12 ms,
  ILOOP X w PC_DIST x8 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = DIST ->
  evt psegs (fun ms' => IPOST X (arm_DIST ivar_ref w) ms' /\ PATG X (wof (arm_DIST ivar_ref w))) ms.
Proof.
  intros X [s c r] x8 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  pose proof (WINV_dist_okb _ HW HM) as OKB. unfold dist_okb in OKB. cbn [w_s w_c w_r] in OKB.
  pose proof HW as (HCORE & HREGS & HMF & _). cbn [w_s w_c w_r] in *.
  rewrite HM in HMF. unfold MF in HMF. cbn in HMF. destruct HMF as (_ & _ & [_ TD] & _).
  pose proof (cpok_ofs_ok _ _ _ _ TD) as CPO.
  pose proof HP as (_ & _ & _ & _ & _ & _ & Pin & Pin1 & _). cbn [w_s w_c w_r] in *.
  pose proof HREGS as (Rn0 & Rh0 & Rnh0 & _ & _ & _ & [RB0 RH0] & Rin & _).
  destruct (decode_okb_lvl1 _ _ _ _ _ _ OKB) as [RN D1].
  destruct (dchk 8 c (dec_idx1 (is_distbits s)) code_bits (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r) as [rf1|] eqn:HD1; [clear D1| contradiction].
  rewrite arm_DIST_eq. change (DECODE1 (is_distcode s) (is_distbits s)) with (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits).
  eapply evt_cut; [exact (dist_lvl1 X s c r rf1 x8 x12 ms HL XO HREGS HP RN CPO HD1)|].
  intros ms1 [(r1 & q1 & ED1 & -> & KB1 & RI1 & HREGS1 & HPL1 & HJ1 & HQ1)|(r1 & ED1 & HPL1 & HLV)].
  2:{ rewrite ED1. apply evt_done. split; [exact HLV|]. cbn [wof]. eapply PATG_pulled; [exact HP| exact HPL1]. }
  rewrite ED1.
  destruct (decG_r1_facts c r r1 HREGS1 HPL1) as ((RNX1 & RHV1 & RNH1 & RB1 & RHB1) & EI1 & EO1 & ER1 & EP1 & EL1).
  assert (HN0 : dist_next (mkW s c r) =
                if dist_two (code_op (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) then
                  match DECODE_k 8 (is_distcode s) (dec_idx2 (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))))
                                 (dec_need2 (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))) (mkW s c r1) with
                  | ARun here (mkW _ _ r2) => dist_tailnext s c here (ddrop r2 (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))))
                                                (addback s (code_bits (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1)))))
                  | _ => None
                  end
                else dist_tailnext s c (code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) r1 s).
  { unfold dist_next. cbn [w_s w_c w_r]. change (DECODE1 (is_distcode s) (is_distbits s)) with (DECODE_k 8 (is_distcode s) (dec_idx1 (is_distbits s)) code_bits).
    rewrite ED1. reflexivity. }
  set (last := code_at s (is_distcode s) (dec_idx1 (is_distbits s) (ir_hold r1))) in *.
  pose proof (code_bits_range last) as RLB.
  pose proof (REGS_hold64 c r1 HREGS1) as RH1.
  change (Z.land (code_op last) 240 =? 0) with (dist_two (code_op last)).
  change (DECODE2 (is_distcode s) last) with (DECODE_k 8 (is_distcode s) (dec_idx2 last) (dec_need2 last)).
  destruct (dist_two (code_op last)) eqn:TWO.
  -
    destruct (decode_okb_lvl2 _ _ _ _ _ _ r1 OKB HD1 KB1 TWO) as [K31 D2]. fold last in K31, D2.
    destruct (dchk 8 c (dec_idx2 last) (dec_need2 last) (ctab_size (is_distcode s)) (code_at s (is_distcode s)) r1) as [rf2|] eqn:HD2; [clear D2| contradiction].
    eapply evt_cut; [exact (dist_lvl2 X s c r r1 rf2 q1 ms1 HJ1 HQ1 XO HP EI1 EO1 EP1 EL1 ER1 HREGS1 RI1 CPO last eq_refl TWO KB1 K31 HD2)|].
    intros ms2 [(r2 & q2 & ED2 & -> & KB2 & RI2 & HREGS2 & HPL2 & HJ2 & HQ2)|(r2 & ED2 & HPL2 & HLV)].
    2:{ rewrite ED2. apply evt_done. split; [exact HLV|]. cbn [wof].
        eapply PATG_pulled; [exact HP| exact (pulled_trans r r1 r2 (proj1 RB0) HPL1 HPL2)]. }
    rewrite ED2. rewrite ED2 in HN0.
    destruct (decG_r1_facts c r1 r2 HREGS2 HPL2) as ((RNX2 & RHV2 & RNH2 & RB2 & RHB2) & EI2 & EO2 & ER2 & EP2 & EL2).
    pose proof (REGS_hold64 c r2 HREGS2) as RH2.
    set (e2 := code_at s (is_distcode s) (dec_idx2 last (ir_hold r2))) in *. pose proof (code_bits_range e2) as RHB.
    assert (KB2' : code_bits last + code_bits e2 <= ir_bits r2) by (unfold dec_need2 in KB2; rewrite wrap32_id in KB2 by lia; exact KB2).
    eapply evt_cut; [exact (dist_j2 X s c r r2 last q2 ms2 HJ2 HQ2 XO RI2 CPO ltac:(lia) RH2)|].
    intros ms3 (q3 & HJ3 & HQ3). fold e2 in HQ3.
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9).
    pose proof (bv_swrap32_range (is_back s)) as RBK.
    refine (dist_fin X s c r (ddrop r2 (code_bits last)) e2 (addback s (code_bits last)) _ q3 ms3 HJ3 HQ3 XO HW HP HM _ _ _ _ _ eq_refl (le4_back_add2 (is_back s) (code_bits last) (code_bits e2)) _ _ F7 _ _ HN0);
      try congruence; try lia.
  -
    eapply evt_cut; [exact (dist_direct X s c r r1 q1 ms1 HJ1 HQ1 XO RI1 CPO TWO)|].
    intros ms3 (q3 & HJ3 & HQ3). fold last in HQ3.
    pose proof (bv_swrap32_range (is_back s)) as RBK.
    refine (dist_fin X s c r r1 last s _ q3 ms3 HJ3 HQ3 XO HW HP HM EI1 EO1 ER1 EP1 EL1 eq_refl (le4_back_add (is_back s) (code_bits last)) _ _ RH1 _ _ HN0); lia.
Qed.

Lemma arm_DIST_of : forall flush, arm_stmtg flush DIST PC_DIST (arm_DIST ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (dist_core X w _ x12 ms HL XO HW HP HM). Qed.
End Dist.
