From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_ikit Z_infl_defs Zg_infl_defs Z_ukit Z_infl_pure Z_infl_pure2 Zh_kit Z_infl_c_pure Z_infl_c_tab Z_infl_a_dist1 Z_infl_a_dist Z_infl_a_lenext Z_infl_a_len1 Zg_infl_t_iface Zg_infl_c_kit Zg_infl_a_len1.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import RefInflateSafeH ZProg ZIface InflateState InflateArms Inflate RefInflateSafeD RefInflateSafeTY RefInflateArmLib RefInflateOkb RefInflateA_DIST1 RefInflateA_DIST2 RefInflateA_DIST RefInflateA_LENEXT RefInflateA_LEN1 RefInflateA_LEN RefInflateSafeOK RefInflateSafeOK2 InffastMem.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition lt_s1 (s : inflate_state) (here Bv : Z) : inflate_state := iset_length (iset_back s (Bv + code_bits here)) (code_val here).
Definition lt_lx (s : inflate_state) (c : icall) (here : Z) (rt : iregs) (Bv : Z) : iw :=
  mkW (iset_mode (iset_extra (lt_s1 s here Bv) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)).
Local Ltac close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM :=
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK
  | eexists _, _, _, _, _; unfold izs_call_cells, izs_priv_cells, Z_ZCALLOC, Z_ZCFREE; cbn [app]; inorm; close_cells ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| unfold isT, isT_cells; exists padT; inorm; close_cells GT
                        | exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Lemma len_tail_walk : forall X sb c r0 rt here Bv q ms,
  ILOOPh X (mkW sb c r0) PC_LEN_T q ms -> len_QT X here rt Bv r0 q -> ix_ok X -> (is_window_blk sb <> None -> ix_hasw X = true) ->
  ir_in rt = ir_in r0 -> ir_out rt = ir_out r0 -> ir_ret rt = ir_ret r0 -> ir_put rt = ir_put r0 -> ir_left rt = ir_left r0 ->
  0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r0 <= Z.of_nat (length (ix_rest0 X)) ->
  evt usegs (fun ms' =>
     if code_op here =? 0 then exists x26 x12, ILOOP X (mkW (iset_mode (lt_s1 sb here Bv) LIT) c (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if negb (Z.land (code_op here) 32 =? 0)
     then exists x26 x12, ILOOP X (mkW (iset_mode (iset_back (lt_s1 sb here Bv) (-1)) TYPE) c (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if negb (Z.land (code_op here) 64 =? 0)
     then exists x26 x12, ILOOP X (mkW (iset_mode (lt_s1 sb here Bv) BAD) (icset_msg c MSG_invalid_literal_length_code) (ddrop rt (code_bits here))) PC_DISPATCH x26 x12 ms'
     else if Z.land (code_op here) 15 =? 0
     then exists q', ILOOPh X (lt_lx sb c here rt Bv) PC_LENEXT_OFF q' ms' /\ LXO X (ddrop rt (code_bits here)) q'
     else exists q', ILOOPh X (lt_lx sb c here rt Bv) PC_LENEXT_NB q' ms'
                     /\ LXE X (w_s (lt_lx sb c here rt Bv)) (ddrop rt (code_bits here)) q') ms.
Proof.
  intros X sb c r0 rt here Bv [x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31] ms HL HQ XO Pwin
         EI EO ER EP EL RBv RB RH RHV RNX RPUT.
  destruct HQ as (E19 & E29 & E28 & E7 & E11 & E22 & E12 & E14 & E9 & E10).
  cbn [h5 h6 h7 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h28 h29 h30 h31] in *.
  subst x19 x29 x28 x7 x11 x22 x12 x14 x9 x10.
  apply (ILOOPh_regs X sb c r0 rt) in HL; [|assumption..].
  iarm_openh HL.
  pose proof (code_op_range here) as ROP. pose proof (code_val_range here) as RVAL. pose proof (code_bits_range here) as RBITS. pose proof (code_w_range here) as RW.
  pose proof (land32_cases (code_op here) ROP) as R32. pose proof (land64_cases (code_op here) ROP) as R64. pose proof (land15_range (code_op here)) as R15.
  ix_open XO. unfold PC_LEN_T.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put rt) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. open_isT GT. open_izs ZS.
  pose proof (munch_refl [(il_S (ix_L X), il_S (ix_L X) + 112); (ix_lo X, bv_unsigned (ix_sp X)); (il_As (ix_L X), il_As (ix_L X) + 168);
                          (il_As (ix_L X) + 7160, il_As (ix_L X) + 7176)] m) as MUf.
  pose proof (wmono_refl usegs m) as WMf.
  zs. rewrite (code_w_g192 here) by lia. gF.
  zs. rewrite code_w_val. zs. rewrite (code_w_g63 here) by lia. zs. rewrite (code_w_g63 here) by lia.
  do 5 zs.
  zstep. br_cases K0.
  -
    replace (code_op here =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    do 8 zs. itr_groups MUf WMf.
    apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
    close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
  - replace (code_op here =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    do 3 zs. zstep. br_cases K32.
    +
      replace (Z.land (code_op here) 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
      do 9 zs. itr_groups MUf WMf.
      apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
      close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
    + replace (Z.land (code_op here) 32 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
      zs. zstep. br_cases K64.
      *
        replace (Z.land (code_op here) 64 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb].
        do 8 zs. itr_groups MUf WMf.
        apply evt_done. eexists _, _. eapply ILOOP_intro; unfold lt_s1, ddrop; ired; [ireg .. |].
        close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
      * replace (Z.land (code_op here) 64 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb].
        do 4 zs. zstep. br_cases K15.
        -- replace (Z.land (code_op here) 15 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
           itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]
                                          | unfold LXO, ddrop; cbn [h9 h10 h12 h14 h18 h22 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold]; repeat split; try reflexivity; ireg].
           close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
        -- replace (Z.land (code_op here) 15 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
           zs. itr_groups MUf WMf.
           apply evt_done. eexists. split; [eapply ILOOPh_intro; unfold lt_lx, lt_s1, ddrop; ired; [ireg .. |]
                                          | unfold LXE, lt_lx, lt_s1, ddrop; cbn [w_s h9 h10 h11 h12 h14 h18 h22 ir_bits ir_hold ir_have ir_next ir_put irset_bits irset_hold is_extra iset_mode iset_extra iset_length iset_back]; repeat split; try reflexivity; ireg].
           close_all j0 jf FRM STK ZS GA GT padT Gl Gw Gc Gwin ARRS LAY IN OUT MU WM.
Qed.
Section Len.
Hypothesis LENEXT_ON : lenext_core_on_stmt.
Hypothesis LENEXT_OFF : lenext_core_off_stmt.
Hypothesis LEN_FAST : len_fast_stmt.
Lemma len_fin : forall X s0 sb c r rt here Bv q ms,
  ILOOPh X (mkW sb c r) PC_LEN_T q ms -> len_QT X here rt Bv r q -> ix_ok X -> PATG X (mkW s0 c r) -> is_flags s0 = 0 ->
  is_window_blk sb = is_window_blk s0 -> is_back sb = Bv -> (forall B, iset_back sb B = iset_back s0 B) ->
  ir_in rt = ir_in r -> ir_out rt = ir_out r -> ir_ret rt = ir_ret r -> ir_put rt = ir_put r -> ir_left rt = ir_left r ->
  0 <= Bv < 256 ->
  code_bits here <= ir_bits rt <= 63 -> 0 <= ir_hold rt < 2^64 -> 0 <= ir_have rt < 2^32 -> 0 <= ir_next rt ->
  0 <= ir_put r <= Z.of_nat (length (ix_rest0 X)) ->
  (forall w2, len_tailnext c here rt sb = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT) ->
  evt usegs (fun ms' => IPOST X (len_tail c here rt sb) ms' /\ PATG X (wof (len_tail c here rt sb))) ms.
Proof.
  intros X s0 sb c r rt here Bv q ms HL HQ XO HP Pf0 EWB EBV ESBB EI EO ER EP EL RBv RB RH RHV RNX RPUT HWN.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  pose proof (code_bits_range here) as RBITS. pose proof (code_op_range here) as ROP. pose proof (land15_range (code_op here)) as R15.
  eapply evt_cut; [exact (len_tail_walk X sb c r rt here Bv q ms HL HQ XO ltac:(rewrite EWB; exact Pwin) EI EO ER EP EL RBv RB RH RHV RNX RPUT)|].
  intros ms1 H1. unfold len_tail. unfold len_tailnext in HWN. cbv zeta.
  assert (ESB : addback sb (code_bits here) = iset_back s0 (Bv + code_bits here)).
  { unfold addback. rewrite EBV, swrap32_id by lia. apply ESBB. }
  rewrite ESB. rewrite ESB in HWN. unfold lt_lx, lt_s1 in H1. rewrite !ESBB in H1.
  set (Bm := Bv + code_bits here) in *. assert (RBm : 0 <= Bm <= 510) by (subst Bm; lia).
  destruct (code_op here =? 0).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LIT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (negb (Z.land (code_op here) 32 =? 0)).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold TYPE, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (negb (Z.land (code_op here) 64 =? 0)).
  { destruct H1 as (x26' & x12' & H1). apply evt_done. split; [cbn [IPOST]; exists x26', x12'; exact H1|]. cbn [wof].
    eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold BAD, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  cbn [orb] in HWN. destruct (HWN _ eq_refl) as [HW3 HM3].
  assert (HP3 : PATG X (mkW (iset_mode (iset_extra (iset_length (iset_back s0 Bm) (code_val here)) (Z.land (code_op here) 15)) LENEXT) c (ddrop rt (code_bits here)))).
  { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LENEXT, FLAGS, HCRC; cbn; lia| reflexivity| reflexivity| reflexivity| exact EP| reflexivity| exact EO| exact EL| reflexivity| exact Pisr|].
    unfold bk_ok, bkmax. cbn -[Z.le Z.add Z.opp]. intros _. lia. }
  destruct (Z.eqb_spec (Z.land (code_op here) 15) 0) as [E0|NE0].
  - destruct H1 as (q' & H1 & HE). exact (LENEXT_OFF X _ q' ms1 H1 HE XO HW3 HP3 HM3 E0).
  - destruct H1 as (q' & H1 & HE). exact (LENEXT_ON X _ q' ms1 H1 HE XO HW3 HP3 HM3 NE0).
Qed.
Lemma len_core : forall X w q ms,
  ILOOPh X w PC_LEN q ms -> DE X (w_r w) q -> h13 q = wz (il_S (ix_L X)) -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN ->
  evt usegs (fun ms' => IPOST X (arm_LEN ivar_ref w) ms' /\ PATG X (wof (arm_LEN ivar_ref w))) ms.
Proof.
  intros X [s c r] q ms HL HE E13 XO HW HP HM. cbn [w_s w_r] in HM, HE.
  destruct (Z.le_gt_cases 6 (ir_have r)) as [GH|GH];
    [destruct (Z.le_gt_cases 258 (ir_left r)) as [GL|GL]; [destruct (Z.lt_ge_cases (ir_bits r) 8) as [GB|GB]|]|].
  { rewrite (arm_LEN_fast s c r GH GL GB). exact (LEN_FAST X s c r q ms HL HE E13 XO HW HP HM GH GL GB). }
  all: clear E13.
  all: assert (HSLOW : ir_have r < 6 \/ ir_left r < 258 \/ 8 <= ir_bits r) by lia.
  all: clear GH; try clear GL; try clear GB.
  all: pose proof (WINV_len_okb _ HW HM) as OKB; unfold len_okb in OKB; cbn [w_s w_c w_r] in OKB.
  all: pose proof HW as (HCORE & HREGS & HMF & _); cbn [w_s w_c w_r] in *.
  all: rewrite HM in HMF; unfold MF in HMF; cbn in HMF; destruct HMF as (_ & _ & [TL _]).
  all: pose proof (cpok_ofs_ok _ _ _ _ TL) as CPO.
  all: pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK); cbn [w_s w_c w_r] in *.
  all: assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  all: pose proof HREGS as (Rn0 & Rh0 & Rnh0 & Rp0 & Rl0 & Rpl0 & [RB0 RH0] & Rin & _).
  all: assert (RPUT : 0 <= ir_put r <= Z.of_nat (length (ix_rest0 X))) by lia.
  all: replace ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false in OKB
         by (symmetry; apply Bool.not_true_iff_false; intro T; apply andb_prop in T; destruct T as [T T3];
             apply andb_prop in T; destruct T as [T1 T2]; apply Z.leb_le in T1, T2; apply Z.ltb_lt in T3; lia).
  all: apply andb_prop in OKB; destruct OKB as [OKB OKD]; apply andb_prop in OKB; destruct OKB as [OKB _]; apply andb_prop in OKB; destruct OKB as [OKB _].
  all: apply andb_prop in OKB; destruct OKB as [RN1 RN2]; apply Z.leb_le in RN1, RN2.
  all: rewrite (arm_LEN_slow s c r HSLOW); cbv zeta.
  all: set (s0 := iset_back s 0) in *.
  all: assert (OKD0 : decode_okb len_two s0 c r (is_lencode s0) (is_lenbits s0) = true) by exact OKD.
  all: change (is_lencode s) with (is_lencode s0); change (is_lenbits s) with (is_lenbits s0).
  all: assert (HP0 : PATG X (mkW s0 c r))
    by (eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| cbn; rewrite HM; unfold LEN, FLAGS, HCRC; lia| reflexivity..| |exact Pisr|];
        [ cbn [is_mode s0 iset_back]; rewrite HM; reflexivity
        | unfold bk_ok; cbn [is_back is_mode s0 iset_back]; pose proof (bkmax_range (is_mode s)); lia ]).
  all: destruct (decode_okb_lvl1 _ _ _ _ _ _ OKD0) as [RN D1].
  all: destruct (dchk 8 c (dec_idx1 (is_lenbits s0)) code_bits (ctab_size (is_lencode s0)) (code_at s0 (is_lencode s0)) r) as [rf1|] eqn:HD1; [clear D1| contradiction].
  all: change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits).
  all: eapply evt_cut; [exact (len_pre X s c r q ms HL HE XO HREGS HP ltac:(lia) HSLOW)|].
  all: intros ms0 (q0 & HL0 & HE0 & E11 & E12).
  all: eapply evt_cut; [exact (len_lvl1 X s0 c r rf1 q0 ms0 HL0 HE0 E11 E12 XO HREGS HP0 RN CPO HD1)|].
  all: intros ms1 [(r1 & q1 & ED1 & -> & KB1 & RI1 & HREGS1 & HPL1 & HJ1 & HQ1)|(r1 & ED1 & HPL1 & HLV)];
    [| rewrite ED1; apply evt_done; split; [exact HLV|]; cbn [wof]; eapply PATG_pulled; [exact HP0| exact HPL1] ].
  all: rewrite ED1.
  all: destruct (decG_r1_facts c r r1 HREGS1 HPL1) as ((RNX1 & RHV1 & RNH1 & RB1 & RHB1) & EI1 & EO1 & ER1 & EP1 & EL1).
  all: pose proof (ILOOPh_regs X s0 c r1 r _ q1 ms1 HJ1 (eq_sym EI1) (eq_sym EO1) (eq_sym ER1) (eq_sym EP1) (eq_sym EL1)) as HJ1r.
  all: assert (HN0 : len_next (mkW s c r) =
                if len_two (code_op (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) then
                  match DECODE_k 8 (is_lencode s0) (dec_idx2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))))
                                 (dec_need2 (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))) (mkW s0 c r1) with
                  | ARun here (mkW _ _ r2) => len_tailnext c here (ddrop r2 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                                                (addback s0 (code_bits (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1)))))
                  | _ => None
                  end
                else len_tailnext c (code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) r1 s0)
    by (unfold len_next; cbn [w_s w_c w_r]; cbv zeta;
        replace ((6 <=? ir_have r) && (258 <=? ir_left r) && (ir_bits r <? 8)) with false
          by (symmetry; apply Bool.not_true_iff_false; intro T; apply andb_prop in T; destruct T as [T T3];
              apply andb_prop in T; destruct T as [T1 T2]; apply Z.leb_le in T1, T2; apply Z.ltb_lt in T3; lia);
        fold s0; change (is_lencode s) with (is_lencode s0); change (is_lenbits s) with (is_lenbits s0);
        change (DECODE1 (is_lencode s0) (is_lenbits s0)) with (DECODE_k 8 (is_lencode s0) (dec_idx1 (is_lenbits s0)) code_bits);
        rewrite ED1; reflexivity).
  all: set (last := code_at s0 (is_lencode s0) (dec_idx1 (is_lenbits s0) (ir_hold r1))) in *.
  all: pose proof (code_bits_range last) as RLB; pose proof (code_op_range last) as RLO.
  all: pose proof (REGS_hold64 c r1 HREGS1) as RH1.
  all: change (negb (code_op last =? 0) && (Z.land (code_op last) 240 =? 0)) with (len_two (code_op last)).
  all: change (DECODE2 (is_lencode s0) last) with (DECODE_k 8 (is_lencode s0) (dec_idx2 last) (dec_need2 last)).
  all: assert (HWN : forall sbx herex rtx, len_next (mkW s c r) = len_tailnext c herex rtx sbx ->
                forall w2, len_tailnext c herex rtx sbx = Some w2 -> WINV w2 /\ is_mode (w_s w2) = LENEXT)
    by (intros sbx herex rtx E w2 E2; rewrite <- E in E2; exact (len_next_WINV _ _ HW HM E2)).
  all: destruct (len_two (code_op last)) eqn:TWO.
  1,3,5:
    destruct (decode_okb_lvl2 _ _ _ _ _ _ r1 OKD0 HD1 KB1 TWO) as [K31 D2]; fold last in K31, D2;
    (destruct (dchk 8 c (dec_idx2 last) (dec_need2 last) (ctab_size (is_lencode s0)) (code_at s0 (is_lencode s0)) r1) as [rf2|] eqn:HD2; [clear D2| contradiction]);
    (eapply evt_cut; [exact (len_lvl2 X s0 c r r1 rf2 q1 ms1 HJ1 HQ1 XO HP0 EP1 HREGS1 RI1 CPO last eq_refl TWO KB1 K31 HD2)|]);
    (intros ms2 [(r2 & q2 & ED2 & -> & KB2 & RI2 & HREGS2 & HPL2 & HJ2 & HQ2)|(r2 & ED2 & HPL2 & HLV)];
      [| rewrite ED2; apply evt_done; split; [exact HLV|]; cbn [wof]; eapply PATG_pulled; [exact HP0| exact (pulled_trans r r1 r2 (proj1 RB0) HPL1 HPL2)] ]);
    rewrite ED2; rewrite ED2 in HN0;
    destruct (decG_r1_facts c r1 r2 HREGS2 HPL2) as ((RNX2 & RHV2 & RNH2 & RB2 & RHB2) & EI2 & EO2 & ER2 & EP2 & EL2);
    pose proof (REGS_hold64 c r2 HREGS2) as RH2;
    pose proof (ILOOPh_regs X s0 c r2 r _ q2 ms2 HJ2 ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence) ltac:(congruence)) as HJ2r;
    set (e2 := code_at s0 (is_lencode s0) (dec_idx2 last (ir_hold r2))) in *; pose proof (code_bits_range e2) as RHB;
    (assert (KB2' : code_bits last + code_bits e2 <= ir_bits r2) by (unfold dec_need2 in KB2; rewrite wrap32_id in KB2 by lia; exact KB2));
    (eapply evt_cut; [exact (len_j2 X s0 c r r1 r2 last q2 ms2 HJ2r HQ2 XO HP0 RI2 CPO ltac:(lia) RH2 ltac:(lia) K31 RPUT EP1)|]);
    intros ms3 (q3 & HJ3 & HQ3); fold e2 in HQ3;
    destruct (ddrop_facts' r2 (code_bits last) ltac:(lia) ltac:(lia) RH2) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9);
    rewrite (addback0 s0 (code_bits last) eq_refl RLB); rewrite (addback0 s0 (code_bits last) eq_refl RLB) in HN0;
    (refine (len_fin X s0 (iset_back s0 (code_bits last)) c r (ddrop r2 (code_bits last)) e2 (code_bits last) q3 ms3 HJ3 HQ3 XO HP0 Pf0 eq_refl eq_refl (fun B => eq_refl) _ _ _ _ _ _ _ F7 _ _ RPUT (HWN _ _ _ HN0));
      try congruence; try lia).
  all:
    (eapply evt_cut; [exact (len_direct X s0 c r r1 q1 ms1 HJ1r HQ1 XO TWO)|]);
    intros ms3 (q3 & HJ3 & HQ3); fold last in HQ3;
    (refine (len_fin X s0 s0 c r r1 last 0 q3 ms3 HJ3 HQ3 XO HP0 Pf0 eq_refl eq_refl (fun B => eq_refl) EI1 EO1 ER1 EP1 EL1 _ _ RH1 _ _ RPUT (HWN _ _ _ HN0)); lia).
Qed.
Lemma arm_LEN_of : forall flush, arm_stmtg flush LEN PC_LEN (arm_LEN ivar_ref).
Proof.
  intros flush X w x12 ms _ HL XO HW _ HP HM. destruct (ILOOPh_of_ILOOP _ _ _ _ _ _ HL) as (q & HLh & _ & _ & HH).
  pose proof HH as (_ & _ & _ & E13 & _).
  exact (len_core X w q ms HLh (DE_of_hhome _ _ _ HH) E13 XO HW HP HM).
Qed.
Lemma len__core : forall X w x26 x12 ms,
  ILOOP X w PC_LEN_ x26 x12 ms -> ix_ok X -> WINV w -> PATG X w -> is_mode (w_s w) = LEN_ ->
  evt usegs (fun ms' => IPOST X (arm_LEN_ ivar_ref w) ms' /\ PATG X (wof (arm_LEN_ ivar_ref w))) ms.
Proof.
  intros X [s c r] x26 x12 ms HL XO HW HP HM. cbn [w_s] in HM.
  rewrite arm_LEN__eq.
  pose proof (WINV_LEN_ s c r HW HM) as HW2.
  pose proof HP as (Pw & Pwb & Phd & Pfl & Pgz & Pwin & Pin & Pin1 & Pout & Pout1 & Pisr & POBY & PBK). cbn [w_s w_c w_r] in *.
  assert (Pf0 : is_flags s = 0) by (destruct Pfl as [Pf|(Pf & [E|E] & _)]; [exact Pf| |]; rewrite HM in E; discriminate E).
  assert (HP2 : PATG X (mkW (iset_mode s LEN) c r)).
  { eapply PATG_step; [exact HP| reflexivity| reflexivity| reflexivity| exact Pf0| unfold LEN, FLAGS, HCRC; cbn; lia| reflexivity..| exact Pisr| bk_keep]. }
  eapply (evt_cut usegs (fun ms1 => exists q, ILOOPh X (mkW (iset_mode s LEN) c r) PC_LEN q ms1 /\ DE X r q /\ h13 q = wz (il_S (ix_L X)))).
  2:{ intros ms1 (q & H1 & HE & E13). exact (len_core X _ q ms1 H1 HE E13 XO HW2 HP2 eq_refl). }
  pose proof HW as (_ & HREGS & _). cbn [w_s w_c w_r] in HREGS. destruct HREGS as (Rn & Rh & Rnh & Rp & Rl & Rpl & _).
  clear HW HW2 HP HP2 Pfl Pgz Pisr POBY PBK.
  iarm_open HL. ix_open XO. unfold PC_LEN_.
  pose proof (av8_zlength (ix_input X) (arr_len (ix_input X)) ltac:(lia)) as LIN.
  pose proof (iout_bytes_length (ix_rest0 X) c (ir_put r) ltac:(lia)) as LOB. apply (f_equal Z.of_nat) in LOB.
  open_IST ST. open_isA GA. ifine m.
  do 2 zs.
  itr_groups MUf WMf.
  apply evt_done. eexists. split; [eapply ILOOPh_intro; ired; [ireg .. |] | unfold DE; cbn [h9 h10 h13 h18 h22 h24 h25]; repeat split; reflexivity].
  apply IMEM_intro; inorm;
  [ exists j0, jf; exact FRM | exact STK | exact ZS
  | constructor; inorm; [unfold isA, isA_cells; inorm; close_cells GA| exact GT| exact Gl| exact Gw| exact Gc| exact Gwin| exact ARRS| exact LAY]
  | exact IN | unfold iout; exact OUT | eassumption | exact MU | exact WM ].
Qed.
Lemma arm_LEN__of : forall flush, arm_stmtg flush LEN_ PC_LEN_ (arm_LEN_ ivar_ref).
Proof. intros flush X w x12 ms _ HL XO HW _ HP HM. exact (len__core X w _ x12 ms HL XO HW HP HM). Qed.
Lemma len_core_ok : len_core_stmt.
Proof. exact len_core. Qed.
Lemma len__core_ok : len__core_stmt.
Proof. exact len__core. Qed.
End Len.
